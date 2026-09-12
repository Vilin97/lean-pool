/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part16A

/-! # GapCVP proof, part 16, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness

open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness

open GapCVP.PhysicalShiftedSourceColumnGridProjection

open GapCVP.PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness

open GapCVP.PhysicalShiftedInterpolationBaseInstantiation

open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness

open GapCVP.PhysicalShiftedCanonicalRetainedClauseSourceCorrectness

local notation "retainedClause_source" =>
  paperFormulaRetainedClause_retainedOriginal

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

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.CanonicalMatrixShape
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalCoefficientCorrectness GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalMatrixCellTM GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalRefinementCheckSourceCorrectness GapCVP.PhysicalRefinementGuardAbsorption
open GapCVP.SourceOrder

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalPhysicalMatrixCellComputerOfGuardedFamilies
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (global refinement ordinary shifted : List Bool → List Bool)
    (globalComputer : BitTM global)
    (refinementComputer : BitTM refinement)
    (ordinaryComputer : BitTM ordinary)
    (shiftedComputer : BitTM shifted)
    (correctGlobal : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
      global (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (row.val < physicalFormulaGlobalBoundary formula) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))])
    (correctRefinement : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
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
    (correctOrdinary : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
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
    (correctShifted : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
      shifted (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤
          row.val) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))]) :
    PaperVariableArityCanonicalBinaryMatrixCellComputer shape :=
  paperVariableArityCanonicalPhysicalMatrixCellComputerOfCheck shape
    (physicalMatrixGuardedFourFamilyCheck
      global refinement ordinary shifted)
    (paperVariableArityPhysicalMatrixGuardedFourFamilyCheckComputable
      global refinement ordinary shifted globalComputer
      refinementComputer ordinaryComputer shiftedComputer)
    (fun formula row column =>
      paperVariableArityPhysicalMatrixGuardedFourFamilyCheck_valid
        global refinement ordinary shifted formula row column
        (correctGlobal formula row column)
        (correctRefinement formula row column)
        (correctOrdinary formula row column)
        (correctShifted formula row column))

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalPhysicalMatrixCellComputerOfActualGlobal
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (refinement ordinary shifted : List Bool → List Bool)
    (refinementComputer : BitTM refinement)
    (ordinaryComputer : BitTM ordinary)
    (shiftedComputer : BitTM shifted)
    (correctRefinement : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
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
    (correctOrdinary : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
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
    (correctShifted : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
      shifted (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤
          row.val) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))]) :
    PaperVariableArityCanonicalBinaryMatrixCellComputer shape :=
  paperVariableArityCanonicalPhysicalMatrixCellComputerOfGuardedFamilies
    shape physicalGlobalCheckBit
    refinement ordinary shifted
    paperVariableArityPhysicalGlobalCheckBitComputable
    refinementComputer ordinaryComputer shiftedComputer
    paperVariableArityPhysicalGlobalCheckBit_valid
    correctRefinement correctOrdinary correctShifted

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityCanonicalPhysicalMatrixCellComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    PaperVariableArityCanonicalBinaryMatrixCellComputer shape :=
  paperVariableArityCanonicalPhysicalMatrixCellComputerOfActualGlobal
    shape
    physicalRefinementCheckBit
    physicalOrdinaryCheckBit
    physicalShiftedCheckBit
    paperVariableArityPhysicalRefinementCheckBitComputable
    paperVariableArityPhysicalOrdinaryCheckBitComputable
    paperVariableArityPhysicalShiftedCheckBitComputable
    paperVariableArityPhysicalRefinementCheckBit_valid
    paperVariableArityPhysicalOrdinaryCheckBit_valid
    paperVariableArityPhysicalShiftedCheckBit_valid

end Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation

namespace Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine

open GapCVP.OriginalThreeSATNPHardness GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.ExactPhysicalSourceTM

/-- GapCVP reduction support. -/
noncomputable def HasIntegerTarget (record : GapCVPInstance) : Bool :=
  @decide (
  ∀ index : Fin record.dimension, ∃ value : ℤ, record.target index = (value : ℚ)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def integerTargetGapCVP400Promise : PromiseProblem where
  yes bits :=
    @decide (
 ∃ record : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode record = bits ∧
      HasIntegerTarget record ∧ gapYES400 record
    ) (Classical.propDecidable _)
  no bits :=
    @decide (
 ∃ record : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode record = bits ∧
      HasIntegerTarget record ∧ gapNO400 record
    ) (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [decide_eq_true_eq] at positive negative
    obtain ⟨first, hfirst, _, hyes⟩ := positive
    obtain ⟨second, hsecond, _, hno⟩ := negative
    have same :=
      (binaryFinEncoding GapCVPInstance).encode_injective
        (hfirst.trans hsecond.symm)
    subst second
    exact gapYES400_not_gapNO400 first hyes hno

private theorem paperVariableArityPhysicalFormulaInstance_hasIntegerTarget
    (encodingLength : ℕ) (formula : ThreeCNF) :
    HasIntegerTarget (physicalFormulaInstance encodingLength formula) := by
  simp only [HasIntegerTarget,
      decide_eq_true_eq] at *
  exact fun index => ⟨(physicalFormulaSystem
    encodingLength formula).effectiveAffineRepresentative index, rfl⟩

private theorem canonicalYesInstance_hasIntegerTarget :
    HasIntegerTarget SourceMachineRouting.canonicalYesInstance := by
  simp only [HasIntegerTarget,
      decide_eq_true_eq] at *
  exact fun _ => ⟨0, rfl⟩

private theorem adaptedCanonicalNoInstance_hasIntegerTarget :
    HasIntegerTarget Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance := by
  simp only [HasIntegerTarget,
      decide_eq_true_eq] at *
  exact fun _ => ⟨1, rfl⟩

private theorem paperVariableArityPhysicalSourceInstance_hasIntegerTarget
    (input : List Bool) :
    HasIntegerTarget (physicalSourceInstance input) := by
  classical
  unfold physicalSourceInstance
  split
  · exact adaptedCanonicalNoInstance_hasIntegerTarget
  · split
    · split
      · exact adaptedCanonicalNoInstance_hasIntegerTarget
      · split
        · split
          · exact canonicalYesInstance_hasIntegerTarget
          · split
            · exact paperVariableArityPhysicalFormulaInstance_hasIntegerTarget _ _
            · exact adaptedCanonicalNoInstance_hasIntegerTarget
        · exact adaptedCanonicalNoInstance_hasIntegerTarget
    · exact adaptedCanonicalNoInstance_hasIntegerTarget

@[irreducible] private def paperVariableArityPhysicalSourceMapMachine :
    BitTM
      paperVariableArityPhysicalSourceMap :=
  paperVariableArityPhysicalSourceMapMachineOfCell
    (paperVariableArityCanonicalPhysicalMatrixCellComputer
      paperCanonicalPhysicalMatrixShape)

private def paperVariableArityPhysicalSourceReduction :
    PromiseReduction paperOriginalThreeSATLanguage gapCVP400Promise :=
  paperVariableArityPhysicalSourceReductionOfMachine
    paperVariableArityPhysicalSourceMapMachine

private def paperVariableArityPhysicalIntegerTargetSourceReduction :
    PromiseReduction paperOriginalThreeSATLanguage integerTargetGapCVP400Promise := by
  let strengthen (input : List Bool) {property : GapCVPInstance → Prop}
      (witness : ∃ record, (binaryFinEncoding GapCVPInstance).encode record =
        paperVariableArityPhysicalSourceMap input ∧ property record) :
      ∃ record, (binaryFinEncoding GapCVPInstance).encode record =
        paperVariableArityPhysicalSourceMap input ∧
          HasIntegerTarget record ∧ property record := by
    obtain ⟨record, encoding, holds⟩ := witness
    cases (binaryFinEncoding GapCVPInstance).encode_injective (encoding.trans rfl)
    exact ⟨_, encoding,
      paperVariableArityPhysicalSourceInstance_hasIntegerTarget input, holds⟩
  exact ⟨paperVariableArityPhysicalSourceMap,
    ⟨paperVariableArityPhysicalSourceMapMachine⟩,
    fun input satisfiable => by
      simp only [integerTargetGapCVP400Promise, decide_eq_true_eq]
      apply strengthen input
      have witness :=
        paperVariableArityPhysicalSourceReduction.completeness input satisfiable
      simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq] at witness
      change ∃ record : GapCVPInstance,
        (binaryFinEncoding GapCVPInstance).encode record =
          paperVariableArityPhysicalSourceMap input ∧ gapYES400 record at witness
      exact witness,
    fun input unsatisfiable => by
      simp only [integerTargetGapCVP400Promise, decide_eq_true_eq]
      apply strengthen input
      have witness :=
        paperVariableArityPhysicalSourceReduction.soundness input unsatisfiable
      simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq] at witness
      change ∃ record : GapCVPInstance,
        (binaryFinEncoding GapCVPInstance).encode record =
          paperVariableArityPhysicalSourceMap input ∧ gapNO400 record at witness
      exact witness⟩

theorem paperVariableArityPhysicalIntegerTargetNPHardPromise :
    NPHardPromise integerTargetGapCVP400Promise :=
  nphardPromise_of_nphard_of_promiseReduction paperOriginalThreeSATIsNPHard
    paperVariableArityPhysicalIntegerTargetSourceReduction
    polynomialTimeClosedUnderComposition

end Factor400BinaryPaperVariableArityUnconditionalPhysicalSourceMachine

namespace Factor400BinaryDecodingPromiseHardness

open scoped BigOperators

open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction

private theorem one_le_binaryCodeGapFactor {blockLength : ℕ}
    (hblock : 0 < blockLength) :
    1 ≤ binaryCodeGapFactor blockLength := by
  unfold binaryCodeGapFactor
  apply Real.one_le_rpow
  · exact_mod_cast hblock
  · norm_num

theorem encodeBinaryNearestCodewordInstance_injective :
    Function.Injective encodeBinaryNearestCodewordInstance := by
  intro left right heq
  have hdecode := congrArg decodeBinaryNearestCodewordInstance heq
  simpa only [decodeBinaryNearestCodewordInstance_encode, Option.some.injEq] using hdecode

theorem encodeBinarySyndromeDecodingInstance_injective :
    Function.Injective encodeBinarySyndromeDecodingInstance := by
  intro left right heq
  have hdecode := congrArg decodeBinarySyndromeDecodingInstance heq
  simpa only [decodeBinarySyndromeDecodingInstance_encode, Option.some.injEq] using hdecode

/-- GapCVP reduction support. -/
noncomputable def binaryNearestCodewordPromise : GapCVP.PromiseProblem where
  yes bits :=
    @decide (
    ∃ record : BinaryNearestCodewordInstance,
      encodeBinaryNearestCodewordInstance record = bits ∧
      0 < record.blockLength ∧ 0 < record.radius ∧
      ∃ coefficients : Fin record.generatorRank → ZMod 2,
        hammingNorm
          (binaryNearestTarget record -
            binaryNearestCodeword record coefficients) ≤ record.radius
    ) (Classical.propDecidable _)
  no bits :=
    @decide (
    ∃ record : BinaryNearestCodewordInstance,
      encodeBinaryNearestCodewordInstance record = bits ∧
      0 < record.blockLength ∧ 0 < record.radius ∧
      ∀ coefficients : Fin record.generatorRank → ZMod 2,
        binaryCodeGapFactor record.blockLength *
            (record.radius : ℝ) <
          (hammingNorm
            (binaryNearestTarget record -
              binaryNearestCodeword record coefficients) : ℝ)
    ) (Classical.propDecidable _)
  disjoint bits hyes hno := by
    simp only [decide_eq_true_eq] at hyes hno
    rcases hyes with ⟨first, hfirst, hblock, _, coefficients, hshort⟩
    rcases hno with ⟨second, hsecond, _, _, hfar⟩
    have heq : first = second :=
      encodeBinaryNearestCodewordInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have hfactor := one_le_binaryCodeGapFactor hblock
    have hradius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have hshortReal :
        (hammingNorm (binaryNearestTarget first -
          binaryNearestCodeword first coefficients) : ℝ) ≤
            (first.radius : ℝ) := by
      exact_mod_cast hshort
    have hscale :
        (first.radius : ℝ) ≤
          binaryCodeGapFactor first.blockLength *
            (first.radius : ℝ) := by
      nlinarith
    linarith [hfar coefficients]

/-- GapCVP reduction support. -/
noncomputable def binarySyndromeDecodingPromise : GapCVP.PromiseProblem where
  yes bits :=
    @decide (
    ∃ record : BinarySyndromeDecodingInstance,
      encodeBinarySyndromeDecodingInstance record = bits ∧
      0 < record.blockLength ∧ 0 < record.radius ∧
      ∃ word : Fin record.blockLength → ZMod 2,
        binarySyndromeProduct record word = binarySyndromeTarget record ∧
          hammingNorm word ≤ record.radius
    ) (Classical.propDecidable _)
  no bits :=
    @decide (
    ∃ record : BinarySyndromeDecodingInstance,
      encodeBinarySyndromeDecodingInstance record = bits ∧
      0 < record.blockLength ∧ 0 < record.radius ∧
      (∃ word : Fin record.blockLength → ZMod 2,
        binarySyndromeProduct record word = binarySyndromeTarget record) ∧
      ∀ word : Fin record.blockLength → ZMod 2,
        binarySyndromeProduct record word = binarySyndromeTarget record →
          binaryCodeGapFactor record.blockLength *
              (record.radius : ℝ) < (hammingNorm word : ℝ)
    ) (Classical.propDecidable _)
  disjoint bits hyes hno := by
    simp only [decide_eq_true_eq] at hyes hno
    rcases hyes with ⟨first, hfirst, hblock, _, word, hsolve, hshort⟩
    rcases hno with ⟨second, hsecond, _, _, _, hfar⟩
    have heq : first = second :=
      encodeBinarySyndromeDecodingInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have hfactor := one_le_binaryCodeGapFactor hblock
    have hradius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have hshortReal : (hammingNorm word : ℝ) ≤ (first.radius : ℝ) := by
      exact_mod_cast hshort
    have hscale :
        (first.radius : ℝ) ≤
          binaryCodeGapFactor first.blockLength *
            (first.radius : ℝ) := by
      nlinarith
    linarith [hfar word hsolve]

theorem integerSquaredNorm_eq_hammingNorm_binaryResidue
    {n : ℕ} (vector : Fin n → ℤ)
    (hbinary : ∀ index, vector index = 0 ∨ vector index = 1) :
    GapCVP.Core.integerSquaredNorm vector =
      hammingNorm (GapCVP.Core.binaryResidue vector) := by
  have hlift :
      binaryWordLift (GapCVP.Core.binaryResidue vector) = vector := by
    funext index
    rcases hbinary index with hzero | hone
    · simp only [binaryWordLift, Core.binaryResidue, hzero, Int.cast_zero, ZMod.val_zero,
        CharP.cast_eq_zero]
    · simp only [binaryWordLift, Core.binaryResidue, hone, Int.cast_one, ZMod.val_one,
        Nat.cast_one]
  calc
    GapCVP.Core.integerSquaredNorm vector =
        GapCVP.Core.integerSquaredNorm
          (binaryWordLift (GapCVP.Core.binaryResidue vector)) := by
      rw [hlift]
    _ = hammingNorm (GapCVP.Core.binaryResidue vector) :=
      integerSquaredNorm_binaryWordLift
        (GapCVP.Core.binaryResidue vector)

/-- GapCVP reduction support. -/
def canonicalBinaryNearestCodewordNo : BinaryNearestCodewordInstance where
  blockLength := 2
  generatorRank := 0
  generator _ index := Fin.elim0 index
  target _ := 1
  radius := 1

private abbrev canonicalBinarySyndromeNo : BinarySyndromeDecodingInstance where
  checkCount := 2
  blockLength := 2
  parityCheck row column := if row = column then 1 else 0
  syndrome _ := 1
  radius := 1

private theorem binaryCodeGapFactor_two_lt_two : binaryCodeGapFactor 2 < 2 := by
  unfold binaryCodeGapFactor
  apply Real.rpow_lt_self_of_one_lt
  · norm_num
  · norm_num

theorem canonicalBinaryNearestCodewordNo_mem :
    binaryNearestCodewordPromise.no
      (encodeBinaryNearestCodewordInstance
        canonicalBinaryNearestCodewordNo) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise,
      decide_eq_true_eq]
  refine ⟨canonicalBinaryNearestCodewordNo, rfl, by decide,
    by decide, ?_⟩
  intro coefficients
  have hcode :
      binaryNearestCodeword canonicalBinaryNearestCodewordNo
        coefficients = 0 := by
    funext index
    simp only [binaryNearestCodeword, canonicalBinaryNearestCodewordNo,
      Pi.zero_apply]
    exact Finset.sum_eq_zero fun column _ => Fin.elim0 column
  have hweight :
      hammingNorm
        (binaryNearestTarget canonicalBinaryNearestCodewordNo -
          binaryNearestCodeword canonicalBinaryNearestCodewordNo
            coefficients) = 2 := by
    rw [hcode, sub_zero]
    change hammingNorm (fun _ : Fin 2 => (1 : ZMod 2)) = 2
    norm_num [hammingNorm]
  rw [hweight]
  simpa only [canonicalBinaryNearestCodewordNo, Nat.cast_one, mul_one, Nat.cast_ofNat, gt_iff_lt]
      using
      binaryCodeGapFactor_two_lt_two

private theorem canonicalBinarySyndromeNo_mem :
    binarySyndromeDecodingPromise.no
      (encodeBinarySyndromeDecodingInstance
        canonicalBinarySyndromeNo) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise,
      decide_eq_true_eq]
  refine ⟨canonicalBinarySyndromeNo, rfl, by decide,
    by decide, ?_, ?_⟩
  · refine ⟨fun _ => 1, ?_⟩
    funext row
    fin_cases row <;>
      decide
  intro word hsolution
  have hword : word = (fun _ : Fin 2 => (1 : ZMod 2)) := by
    funext row
    have hrow := congrFun hsolution row
    fin_cases row <;>
      norm_num [binarySyndromeProduct, canonicalBinarySyndromeNo,
        Fin.sum_univ_two, binarySyndromeTarget] at hrow ⊢
    all_goals assumption
  subst word
  convert binaryCodeGapFactor_two_lt_two using 1 <;>
    norm_num [canonicalBinarySyndromeNo, hammingNorm]

end Factor400BinaryDecodingPromiseHardness

namespace PaperSyndromeInstance

open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.PhysicalWordSoundness

private abbrev paperVariableAritySyndromeInstance
    (encodingLength : ℕ) (formula : ThreeCNF) :
    BinarySyndromeDecodingInstance :=
  let system := physicalWordBinarySystem
    encodingLength formula
  { checkCount := system.rowCount
    blockLength := system.dimension
    parityCheck := system.check
    syndrome := system.rightHandSide
    radius := paperVariableArityIntegerRadius encodingLength formula }

private theorem paperVariableAritySyndromeInstance_completeness
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    binarySyndromeDecodingPromise.yes
      (encodeBinarySyndromeDecodingInstance
        (paperVariableAritySyndromeInstance encodingLength formula)) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise,
      decide_eq_true_eq]
  let system := physicalWordBinarySystem
    encodingLength formula
  obtain ⟨vector, solution, binary, weight⟩ :=
    paperVariableArityPhysicalWordBinarySystem_oneHot_of_satisfiable
      encodingLength formula satisfiable
  refine ⟨paperVariableAritySyndromeInstance encodingLength formula,
    rfl, ?_, ?_, GapCVP.Core.binaryResidue vector, ?_, ?_⟩
  · exact sourceFormulaDimension_pos encodingLength
      (srcFormula formula)
  · exact paperVariableArityIntegerRadius_pos encodingLength formula
  · change system.check.mulVec (GapCVP.Core.binaryResidue vector) =
        system.rightHandSide
    simpa only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq] using solution
  · change hammingNorm (GapCVP.Core.binaryResidue vector) ≤
      paperVariableArityIntegerRadius encodingLength formula
    rw [← integerSquaredNorm_eq_hammingNorm_binaryResidue
      vector binary, weight]

private theorem paperVariableAritySyndromeInstance_soundness
    (encodingLength : ℕ) (formula : ThreeCNF)
    (consistent :
      (physicalWordBinarySystem
        encodingLength formula).effectiveReducedConsistent = true)
    (unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    binarySyndromeDecodingPromise.no
      (encodeBinarySyndromeDecodingInstance
        (paperVariableAritySyndromeInstance encodingLength formula)) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise,
      decide_eq_true_eq]
  let system := physicalWordBinarySystem
    encodingLength formula
  refine ⟨paperVariableAritySyndromeInstance encodingLength formula,
    rfl, ?_, ?_, ?_, ?_⟩
  · exact sourceFormulaDimension_pos encodingLength
      (srcFormula formula)
  · exact paperVariableArityIntegerRadius_pos encodingLength formula
  · refine ⟨GapCVP.Core.binaryResidue system.effectiveAffineRepresentative, ?_⟩
    change system.check.mulVec
      (GapCVP.Core.binaryResidue system.effectiveAffineRepresentative) =
        system.rightHandSide
    simpa only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq] using
      system.effectiveAffineRepresentative_solves consistent
  · intro word solves
    apply lt_of_not_ge
    intro short
    apply unsatisfiable
    apply paperVariableArityPhysicalWordBinarySystem_satisfiable_of_scaled_hamming
      encodingLength formula (binaryWordLift word)
    · simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq]
      change system.check.mulVec
        (GapCVP.Core.binaryResidue (binaryWordLift word)) =
          system.rightHandSide
      rw [binaryResidue_binaryWordLift]
      funext row
      have equation := congrFun solves row
      change
        (∑ column : Fin system.dimension,
          system.check row column * word column) =
            system.rightHandSide row
      exact equation
    · rw [integerSquaredNorm_binaryWordLift]
      have factor_nonnegative :
          0 ≤ binaryCodeGapFactor system.dimension := by
        unfold binaryCodeGapFactor
        positivity
      have radius_nonnegative :
          (0 : ℝ) ≤ (paperVariableArityIntegerRadius
            encodingLength formula : ℝ) := by
        positivity
      change (hammingNorm word : ℝ) ≤
        2 * binaryCodeGapFactor system.dimension *
          (paperVariableArityIntegerRadius encodingLength formula : ℝ)
      change (hammingNorm word : ℝ) ≤
        binaryCodeGapFactor system.dimension *
          (paperVariableArityIntegerRadius encodingLength formula : ℝ)
        at short
      linarith [mul_nonneg factor_nonnegative radius_nonnegative]

end PaperSyndromeInstance

namespace Factor400BinaryDecodingPhysicalWordSourceTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.Factor400BinaryDecodingPromiseReduction GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.GaussianPackedStateTargetAtomTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianPhysicalWordReducedAtomTM GapCVP.Factor400BinaryEffectiveBasisSerializerTM

private def compactPhysicalDecodingBinaryIntegerAtom : List Bool → List Bool :=
  markerConditionalOutput
    (fun _ : List Bool => encodeAtomic (1 : ℤ))
    (encodeAtomic (0 : ℤ))

private noncomputable def compactPhysicalDecodingBinaryIntegerAtomComputable :
    BitTM
      compactPhysicalDecodingBinaryIntegerAtom :=
  markerConditionalComputable
    (sourceFixedWordComputable (encodeAtomic (1 : ℤ)))
    (encodeAtomic (0 : ℤ))

@[simp] private theorem compactPhysicalDecodingBinaryIntegerAtom_false
    (suffix : List Bool) :
    compactPhysicalDecodingBinaryIntegerAtom (false :: suffix) =
      encodeAtomic (0 : ℤ) := by
  rfl

@[simp] private theorem compactPhysicalDecodingBinaryIntegerAtom_true
    (suffix : List Bool) :
    compactPhysicalDecodingBinaryIntegerAtom (true :: suffix) =
      encodeAtomic (1 : ℤ) := by
  rfl

private theorem compactPhysicalDecodingBinaryIntegerAtom_zmod
    (value : ZMod 2) :
    compactPhysicalDecodingBinaryIntegerAtom
        [decide (value = (1 : ZMod 2))] =
      encodeAtomic (value.val : ℤ) := by
  rcases binaryField_zero_or_one value with hzero | hone
  · simp only [hzero, zero_ne_one, decide_false, compactPhysicalDecodingBinaryIntegerAtom_false,
      ZMod.val_zero,
        CharP.cast_eq_zero]
  · subst value
    change encodeAtomic (1 : ℤ) =
      encodeAtomic (((1 : ZMod 2).val : ℕ) : ℤ)
    rfl

/-- GapCVP reduction support. -/
def compactPhysicalDecodingBinaryBasisAtom : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput
      (fun _ : List Bool => encodeAtomic (0 : ℤ))
      (encodeAtomic (1 : ℤ)))
    (encodeAtomic (0 : ℤ))

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalDecodingBinaryBasisAtomComputable :
    BitTM
      compactPhysicalDecodingBinaryBasisAtom :=
  markerConditionalComputable
    (markerConditionalComputable
      (sourceFixedWordComputable (encodeAtomic (0 : ℤ)))
      (encodeAtomic (1 : ℤ)))
    (encodeAtomic (0 : ℤ))

theorem compactPhysicalDecodingBinaryBasisAtom_effective
    (system : GapCVP.Core.BinaryAffineSystem)
    (row column : Fin system.dimension) :
    compactPhysicalDecodingBinaryBasisAtom
        (effectiveGaussianStateBasisTag
          system.effectiveGaussianState row column) =
      encodeAtomic
        (((system.effectiveSquareBasisMatrix row column : ZMod 2).val : ℤ)) := by
  unfold effectiveGaussianStateBasisTag
  rw [effectiveGaussianStatePivotRow_effective,
    effectiveGaussianStatePivotRow_effective]
  cases hrow : system.effectivePivotRowOption row with
  | none =>
      cases hcolumn : system.effectivePivotRowOption column with
      | none =>
          by_cases hdiagonal : row = column
          · simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hdiagonal,
              ↓reduceIte,
                Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hcolumn, Int.cast_one,
                    binaryIntegerLift_one]
          · simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hdiagonal,
              ↓reduceIte,
                Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn, Int.cast_zero,
                    binaryIntegerLift_zero]
      | some pivot =>
          simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput,
              Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn, Int.cast_zero,
                  binaryIntegerLift_zero]
  | some pivot =>
      cases hcolumn : system.effectivePivotRowOption column with
      | none =>
          rcases GapCVP.Core.effectiveBinary_eq_zero_or_one
            (system.effectiveGaussianState.system.check pivot column)
              with hzero | hone
          · simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hzero,
              zero_ne_one, decide_false,
                Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn, ZMod.val_zero,
                    CharP.cast_eq_zero, Int.cast_zero]
          · have hentry :
                system.effectiveSquareBasisMatrix row column = (1 : ℤ) := by
              simp only [GapCVP.Core.BinaryAffineSystem.effectiveSquareBasisMatrix,
                hrow, hcolumn, hone, ZMod.val_one, Nat.cast_one]
            simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hone,
                decide_true, hentry,
                Int.cast_one, binaryIntegerLift_one]
      | some other =>
          by_cases hdiagonal : row = column
          · simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hdiagonal,
              ↓reduceIte,
                Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hcolumn, Int.cast_ofNat,
                    binaryIntegerLift_two]
          · simp only [compactPhysicalDecodingBinaryBasisAtom, markerConditionalOutput, hdiagonal,
              ↓reduceIte,
                Core.BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn, Int.cast_zero,
                    binaryIntegerLift_zero]

private theorem compactPhysicalDecodingAtomic_injective
    {α : Type} [Encodable α] :
    Function.Injective (encodeAtomic (α := α)) := by
  intro first second hequality
  have hdecoded := congrArg
    (readAtomic (α := α)) hequality
  have hfirst : readAtomic (encodeAtomic first) =
      some (first, ([] : List Bool)) := by
    simpa only [List.append_nil] using (readAtomic_append first [])
  have hsecond : readAtomic (encodeAtomic second) =
      some (second, ([] : List Bool)) := by
    simpa only [List.append_nil] using (readAtomic_append second [])
  rw [hfirst, hsecond] at hdecoded
  exact congrArg Prod.fst (Option.some.inj hdecoded)

private theorem compactPhysicalDecodingBinaryIntegerAtom_of_rational
    (input : List Bool) (value : ℤ)
    (hatom : effectiveTargetPackedAtom input =
      encodeAtomic (value : ℚ)) :
    compactPhysicalDecodingBinaryIntegerAtom input =
      encodeAtomic value := by
  cases input with
  | nil =>
      have hrational : (0 : ℚ) = (value : ℚ) :=
        compactPhysicalDecodingAtomic_injective
          (by simpa only [effectiveTargetPackedAtom, markerConditionalOutput] using hatom)
      have hinteger : value = 0 := by
        exact_mod_cast hrational.symm
      simp only [compactPhysicalDecodingBinaryIntegerAtom, markerConditionalOutput, hinteger]
  | cons bit suffix =>
      cases bit with
      | false =>
          have hrational : (0 : ℚ) = (value : ℚ) :=
            compactPhysicalDecodingAtomic_injective
              (by simpa only [effectiveTargetPackedAtom, markerConditionalOutput] using hatom)
          have hinteger : value = 0 := by
            exact_mod_cast hrational.symm
          simp only [compactPhysicalDecodingBinaryIntegerAtom_false, hinteger]
      | true =>
          have hrational : (1 : ℚ) = (value : ℚ) :=
            compactPhysicalDecodingAtomic_injective
              (by simpa only [effectiveTargetPackedAtom, markerConditionalOutput] using hatom)
          have hinteger : value = 1 := by
            exact_mod_cast hrational.symm
          simp only [compactPhysicalDecodingBinaryIntegerAtom_true, hinteger]

/-- GapCVP reduction support. -/
def compactPhysicalDecodingGaussianIntegerTargetAtom :
    List Bool → List Bool :=
  compactPhysicalDecodingBinaryIntegerAtom ∘
    gaussianPackedIndexedTargetBit

/-- GapCVP reduction support. -/
noncomputable def
    compactPhysicalDecodingGaussianIntegerTargetAtomComputable :
    BitTM
      compactPhysicalDecodingGaussianIntegerTargetAtom :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedTargetBitComputable
    compactPhysicalDecodingBinaryIntegerAtomComputable

theorem compactPhysicalDecodingGaussianIntegerTargetAtom_effective
    (system : GapCVP.Core.BinaryAffineSystem)
    (column : Fin system.dimension)
    (source : List Bool) :
    compactPhysicalDecodingGaussianIntegerTargetAtom
        (gaussianPackedIndexedStateWord column.val
          (effectiveGaussianPackedStateWord
            system.effectiveGaussianState source)) =
      encodeAtomic (system.effectiveAffineRepresentative column) := by
  unfold compactPhysicalDecodingGaussianIntegerTargetAtom
  rw [Function.comp_apply]
  apply compactPhysicalDecodingBinaryIntegerAtom_of_rational
  exact gaussianPackedIndexedTargetAtom_effective
    system column source

private def compactPhysicalDecodingBinaryIntegerAtomBound : ℕ :=
  max (encodeAtomic (0 : ℤ)).length
    (encodeAtomic (1 : ℤ)).length

private theorem compactPhysicalDecodingBinaryIntegerAtom_length_le
    (input : List Bool) :
    (compactPhysicalDecodingBinaryIntegerAtom input).length ≤
      compactPhysicalDecodingBinaryIntegerAtomBound := by
  cases input with
  | nil =>
      change (encodeAtomic (0 : ℤ)).length ≤
        max (encodeAtomic (0 : ℤ)).length
          (encodeAtomic (1 : ℤ)).length
      exact Nat.le_max_left _ _
  | cons bit suffix =>
      cases bit with
      | false =>
          change (encodeAtomic (0 : ℤ)).length ≤
            max (encodeAtomic (0 : ℤ)).length
              (encodeAtomic (1 : ℤ)).length
          exact Nat.le_max_left _ _
      | true =>
          change (encodeAtomic (1 : ℤ)).length ≤
            max (encodeAtomic (0 : ℤ)).length
              (encodeAtomic (1 : ℤ)).length
          exact Nat.le_max_right _ _

private theorem compactPhysicalDecodingAtomicRotation_length_le
    (marker : List Bool → List Bool) (bound : ℕ)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ bound)
    (input : List Bool) :
    (fourFamilyOriginalMarkerRotationOutput
      marker input).length ≤ input.length + bound := by
  rw [sourceFourFamilyOriginalMarkerRotationOutput_eq]
  have hfield := sourceFourFamilyFirstFieldSuffix_length_le
    (input ++ marker (firstFieldContents input))
  have hatom := hmarker (firstFieldContents input)
  simp only [List.length_append] at hfield
  omega

private theorem compactPhysicalDecodingAtomicRotation_iterate_length_le
    (marker : List Bool → List Bool) (bound : ℕ)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ bound)
    (seed : List Bool) (stage : ℕ) :
    (((fourFamilyOriginalMarkerRotationOutput
      marker)^[stage]) seed).length ≤
        seed.length + stage * bound := by
  induction stage with
  | zero =>
      simp only [Function.iterate_zero, id_eq, zero_mul, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := compactPhysicalDecodingAtomicRotation_length_le
        marker bound hmarker
          (((fourFamilyOriginalMarkerRotationOutput
            marker)^[stage]) seed)
      simp only [Nat.succ_mul]
      omega

private theorem compactPhysicalDecodingAtomicRotation_polynomiallyBounded
    (marker : List Bool → List Bool) (bound : ℕ)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ bound) :
    PolynomiallyBoundedFoldStates
      (fourFamilyOriginalMarkerRotationOutput marker)
      (Polynomial.C (bound + 1) * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq] at *
  intro input count seed hparse stage hstage
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate :=
    compactPhysicalDecodingAtomicRotation_iterate_length_le
      marker bound hmarker seed stage
  have hstageBound : stage ≤ input.length :=
    hstage.trans hcount
  have hproduct : stage * bound ≤ input.length * bound :=
    Nat.mul_le_mul_right bound hstageBound
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Nat.add_mul, one_mul]
  have hcommuted : stage * bound ≤ bound * input.length := by
    simpa only [Nat.mul_comm] using hproduct
  omega

private noncomputable def compactPhysicalDecodingBoundedAtomicFoldComputable
    {marker : List Bool → List Bool} (bound : ℕ)
    (computer : BitTM marker)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ bound) :
    BitTM
      (boundedRecordFoldOutput
        (fourFamilyOriginalMarkerRotationOutput marker)) :=
  boundedDependentRecordFoldComputable
    (sourceFourFamilyOriginalMarkerRotationComputable computer)
    (Polynomial.C (bound + 1) * Polynomial.X)
    (compactPhysicalDecodingAtomicRotation_polynomiallyBounded
      marker bound hmarker)

private theorem compactPhysicalDecodingEncodeFinValues_eq_flatMap
    {α : Type} [Encodable α]
    (count : ℕ) (values : Fin count → α) :
    encodeFinValues count values =
      (List.finRange count).flatMap
        (fun index => encodeAtomic (values index)) := by
  induction count with
  | zero =>
      simp only [encodeFinValues, List.finRange_zero, List.flatMap_nil]
  | succ count ih =>
      rw [List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map]
      change
        encodeAtomic (values 0) ++
            encodeFinValues count (fun index => values index.succ) =
          encodeAtomic (values 0) ++
            (List.finRange count).flatMap
              (fun index => encodeAtomic (values index.succ))
      rw [ih]

private theorem compactPhysicalDecodingEncodeMatrixRows_eq_flatMap
    (rows columns : ℕ) (matrix : Fin rows → Fin columns → ℤ) :
    encodeMatrixRows rows columns matrix =
      (List.finRange rows).flatMap fun row =>
        (List.finRange columns).flatMap fun column =>
          encodeAtomic (matrix row column) := by
  induction rows with
  | zero =>
      simp only [encodeMatrixRows, List.finRange_zero, List.flatMap_nil]
  | succ rows ih =>
      rw [List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map]
      change
        encodeFinValues columns (matrix 0) ++
            encodeMatrixRows rows columns
              (fun row => matrix row.succ) =
          (List.finRange columns).flatMap
              (fun column => encodeAtomic (matrix 0 column)) ++
            (List.finRange rows).flatMap
              (fun row => (List.finRange columns).flatMap
                (fun column => encodeAtomic (matrix row.succ column)))
      rw [compactPhysicalDecodingEncodeFinValues_eq_flatMap,
        ih]

private def compactPhysicalDecodingFiveFieldOutput
    (first second radius firstPayload secondPayload :
      List Bool → List Bool) (input : List Bool) : List Bool :=
  first input ++
    (second input ++
      (radius input ++ (firstPayload input ++ secondPayload input)))

private noncomputable def compactPhysicalDecodingFiveFieldComputable
    {first second radius firstPayload secondPayload :
      List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second)
    (hradius : BitTM radius)
    (hfirstPayload : BitTM firstPayload)
    (hsecondPayload : BitTM secondPayload) :
    BitTM
      (compactPhysicalDecodingFiveFieldOutput
        first second radius firstPayload secondPayload) := by
  have hphysical := pointwiseAppendComputable hfirst
    (pointwiseAppendComputable hsecond
      (pointwiseAppendComputable hradius
        (pointwiseAppendComputable
          hfirstPayload hsecondPayload)))
  exact hphysical

end Factor400BinaryDecodingPhysicalWordSourceTM

namespace PaperBinaryCodingTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.CanonicalMatrixShape
open GapCVP.CanonicalPhysicalMatrixShape GapCVP.CanonicalSourceCatalogue
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.PaperSyndromeInstance GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.OutputBoundedDependentRecordFold

private def paperCodingCheckCountAtomic : List Bool → List Bool :=
  structuralAtomicNaturalWord ∘
    paperCanonicalPhysicalMatrixShape.rows

private noncomputable def paperVariableArityCodingCheckCountAtomicComputable :
    BitTM
      paperCodingCheckCountAtomic :=
  GapCVP.TMComposition.computableInPolyTime
    paperCanonicalPhysicalMatrixShape.rowsComputable
    structuralAtomicNaturalWriterComputable

private theorem paperVariableArityCodingCheckCountAtomic_valid
    (formula : ThreeCNF) :
    paperCodingCheckCountAtomic (encodeThreeCNF formula) =
      encodeAtomic
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rowCount := by
  unfold paperCodingCheckCountAtomic Function.comp
  rw [paperVariableArityCanonicalPhysicalMatrixShape_rows_valid formula]
  simp only [structuralAtomicNaturalWord,
      List.length_replicate]

/-- GapCVP reduction support. -/
def paperCodingBlockLengthAtomic : List Bool → List Bool :=
  structuralAtomicNaturalWord ∘
    paperCanonicalPhysicalMatrixShape.columns

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityCodingBlockLengthAtomicComputable :
    BitTM
      paperCodingBlockLengthAtomic :=
  GapCVP.TMComposition.computableInPolyTime
    paperCanonicalPhysicalMatrixShape.columnsComputable
    structuralAtomicNaturalWriterComputable

theorem paperVariableArityCodingBlockLengthAtomic_valid
    (formula : ThreeCNF) :
    paperCodingBlockLengthAtomic (encodeThreeCNF formula) =
      encodeAtomic
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).dimension := by
  unfold paperCodingBlockLengthAtomic Function.comp
  rw [paperVariableArityCanonicalPhysicalMatrixShape_columns_valid formula]
  simp only [structuralAtomicNaturalWord, List.length_replicate]

/-- GapCVP reduction support. -/
def paperCodingRadiusAtomic : List Bool → List Bool :=
  structuralAtomicNaturalWord ∘ physicalOneHotWeightUnary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityCodingRadiusAtomicComputable :
    BitTM
      paperCodingRadiusAtomic :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalOneHotWeightUnaryComputable
    structuralAtomicNaturalWriterComputable

theorem paperVariableArityCodingRadiusAtomic_valid
    (formula : ThreeCNF) :
    paperCodingRadiusAtomic (encodeThreeCNF formula) =
      encodeAtomic
        (paperVariableArityIntegerRadius
          (encodeThreeCNF formula).length formula) := by
  unfold paperCodingRadiusAtomic Function.comp
  rw [paperVariableArityPhysicalOneHotWeightUnary_valid formula]
  simp only [structuralAtomicNaturalWord, List.length_replicate]
  unfold paperVariableArityIntegerRadius sourceBinaryDecodingRadius
  rw [paperVariableAritySourceFormula_clauses_length]

private def paperCodingCheckIntegerMarker
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  compactPhysicalDecodingBinaryIntegerAtom ∘
    paperCanonicalBinaryMatrixCheckMarker worker

private noncomputable def paperVariableArityCodingCheckIntegerMarkerComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingCheckIntegerMarker worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixCheckMarkerComputable worker)
    compactPhysicalDecodingBinaryIntegerAtomComputable

private theorem paperVariableArityCodingCheckIntegerMarker_length_le
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (input : List Bool) :
    (paperCodingCheckIntegerMarker worker input).length ≤
      compactPhysicalDecodingBinaryIntegerAtomBound :=
  compactPhysicalDecodingBinaryIntegerAtom_length_le
    (paperCanonicalBinaryMatrixCheckMarker worker input)

private theorem paperVariableArityCodingCheckIntegerMarker_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF)
    (row : Fin
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).dimension) :
    paperCodingCheckIntegerMarker worker
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      encodeAtomic
        (((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column).val : ℤ) := by
  unfold paperCodingCheckIntegerMarker
  rw [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixCheckMarker_valid
      worker formula row column]
  exact compactPhysicalDecodingBinaryIntegerAtom_zmod
    ((physicalWordBinarySystem
      (encodeThreeCNF formula).length formula).check row column)

private def paperCodingRhsIntegerMarker
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  compactPhysicalDecodingBinaryIntegerAtom ∘
    paperCanonicalBinaryMatrixRhsMarker worker

private noncomputable def paperVariableArityCodingRhsIntegerMarkerComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingRhsIntegerMarker worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRhsMarkerComputable worker)
    compactPhysicalDecodingBinaryIntegerAtomComputable

private theorem paperVariableArityCodingRhsIntegerMarker_length_le
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (input : List Bool) :
    (paperCodingRhsIntegerMarker worker input).length ≤
      compactPhysicalDecodingBinaryIntegerAtomBound :=
  compactPhysicalDecodingBinaryIntegerAtom_length_le
    (paperCanonicalBinaryMatrixRhsMarker worker input)

private theorem paperVariableArityCodingRhsIntegerMarker_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF)
    (row : Fin
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).dimension) :
    paperCodingRhsIntegerMarker worker
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      encodeAtomic
        (((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rightHandSide
            row).val : ℤ) := by
  unfold paperCodingRhsIntegerMarker
  rw [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixRhsMarker_valid
      worker formula row column]
  exact compactPhysicalDecodingBinaryIntegerAtom_zmod
    ((physicalWordBinarySystem
      (encodeThreeCNF formula).length formula).rightHandSide row)

private def paperCodingCheckIntegerFold
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  boundedRecordFoldOutput
      (fourFamilyOriginalMarkerRotationOutput
        (paperCodingCheckIntegerMarker worker)) ∘
    paperCanonicalBinaryMatrixCheckFoldPreparation
      paperCanonicalPhysicalMatrixShape

private noncomputable def paperVariableArityCodingCheckIntegerFoldComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingCheckIntegerFold worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixCheckFoldPreparationComputable
      paperCanonicalPhysicalMatrixShape)
    (compactPhysicalDecodingBoundedAtomicFoldComputable
      compactPhysicalDecodingBinaryIntegerAtomBound
      (paperVariableArityCodingCheckIntegerMarkerComputable worker)
      (paperVariableArityCodingCheckIntegerMarker_length_le worker))

private def paperCodingRhsIntegerFold
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  boundedRecordFoldOutput
      (fourFamilyOriginalMarkerRotationOutput
        (paperCodingRhsIntegerMarker worker)) ∘
    paperCanonicalBinaryMatrixRhsFoldPreparation
      paperCanonicalPhysicalMatrixShape

private noncomputable def paperVariableArityCodingRhsIntegerFoldComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingRhsIntegerFold worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRhsFoldPreparationComputable
      paperCanonicalPhysicalMatrixShape)
    (compactPhysicalDecodingBoundedAtomicFoldComputable
      compactPhysicalDecodingBinaryIntegerAtomBound
      (paperVariableArityCodingRhsIntegerMarkerComputable worker)
      (paperVariableArityCodingRhsIntegerMarker_length_le worker))

private def paperCodingCheckIntegerPayload
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  firstFieldSuffix ∘ paperCodingCheckIntegerFold worker

private noncomputable def paperVariableArityCodingCheckIntegerPayloadComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingCheckIntegerPayload worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCodingCheckIntegerFoldComputable worker)
    firstFieldSuffixComputable

private def paperCodingRhsIntegerPayload
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  firstFieldSuffix ∘ paperCodingRhsIntegerFold worker

private noncomputable def paperVariableArityCodingRhsIntegerPayloadComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperCodingRhsIntegerPayload worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCodingRhsIntegerFoldComputable worker)
    firstFieldSuffixComputable

private theorem paperVariableArityCodingCheckIntegerFold_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF) :
    paperCodingCheckIntegerFold worker
        (encodeThreeCNF formula) =
      lengthPrefixedWord (encodeThreeCNF formula) ++
        (paperCanonicalBinaryMatrixCheckQueries
          paperCanonicalPhysicalMatrixShape formula).flatMap
            (paperCodingCheckIntegerMarker worker) := by
  unfold paperCodingCheckIntegerFold
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixCheckFoldPreparation_valid
      paperCanonicalPhysicalMatrixShape formula]
  unfold sourcePhysicalWordPackedQueryPreparation
  simpa only [fourFamilyOriginalMarkerStream] using
      boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries (paperCodingCheckIntegerMarker
          worker)
        (paperCanonicalBinaryMatrixCheckQueries paperCanonicalPhysicalMatrixShape formula)
        (lengthPrefixedWord (encodeThreeCNF formula))

private theorem paperVariableArityCodingRhsIntegerFold_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF) :
    paperCodingRhsIntegerFold worker
        (encodeThreeCNF formula) =
      lengthPrefixedWord (encodeThreeCNF formula) ++
        (paperCanonicalBinaryMatrixRhsQueries
          paperCanonicalPhysicalMatrixShape formula).flatMap
            (paperCodingRhsIntegerMarker worker) := by
  unfold paperCodingRhsIntegerFold
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixRhsFoldPreparation_valid
      paperCanonicalPhysicalMatrixShape formula]
  unfold sourcePhysicalWordPackedQueryPreparation
  simpa only [fourFamilyOriginalMarkerStream] using
      boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries (paperCodingRhsIntegerMarker
          worker)
        (paperCanonicalBinaryMatrixRhsQueries paperCanonicalPhysicalMatrixShape formula)
        (lengthPrefixedWord (encodeThreeCNF formula))

private theorem paperVariableArityCodingCheckIntegerPayload_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF) :
    paperCodingCheckIntegerPayload worker
        (encodeThreeCNF formula) =
      encodeMatrixRows
        (paperVariableAritySyndromeInstance
          (encodeThreeCNF formula).length formula).checkCount
        (paperVariableAritySyndromeInstance
          (encodeThreeCNF formula).length formula).blockLength
        (fun row column => (((paperVariableAritySyndromeInstance
            (encodeThreeCNF formula).length formula).parityCheck row column).val : ℤ)) := by
  unfold paperCodingCheckIntegerPayload
  rw [Function.comp_apply,
    paperVariableArityCodingCheckIntegerFold_valid worker formula,
    firstFieldSuffix_valid]
  simp only [paperVariableAritySyndromeInstance,
    paperCanonicalPhysicalMatrixShape]
  rw [compactPhysicalDecodingEncodeMatrixRows_eq_flatMap]
  unfold paperCanonicalBinaryMatrixCheckQueries
  simp only [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  apply List.flatMap_congr
  intro column _
  exact paperVariableArityCodingCheckIntegerMarker_valid
    worker formula row column

private theorem paperVariableArityCodingRhsIntegerPayload_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF) :
    paperCodingRhsIntegerPayload worker
        (encodeThreeCNF formula) =
      encodeFinValues
        (paperVariableAritySyndromeInstance
          (encodeThreeCNF formula).length formula).checkCount
        (fun row => (((paperVariableAritySyndromeInstance
            (encodeThreeCNF formula).length formula).syndrome row).val : ℤ)) := by
  unfold paperCodingRhsIntegerPayload
  rw [Function.comp_apply,
    paperVariableArityCodingRhsIntegerFold_valid worker formula,
    firstFieldSuffix_valid]
  simp only [paperVariableAritySyndromeInstance,
    paperCanonicalPhysicalMatrixShape]
  rw [compactPhysicalDecodingEncodeFinValues_eq_flatMap]
  unfold paperCanonicalBinaryMatrixRhsQueries
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  let column : Fin
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).dimension :=
    ⟨0, paperCanonicalPhysicalMatrixShape.columnsPositive
      formula⟩
  simpa only [ZMod.natCast_val] using
    paperVariableArityCodingRhsIntegerMarker_valid
      worker formula row column

private def paperSyndromeStructuralSourceWord
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    List Bool → List Bool :=
  compactPhysicalDecodingFiveFieldOutput
    paperCodingCheckCountAtomic
    paperCodingBlockLengthAtomic
    paperCodingRadiusAtomic
    (paperCodingRhsIntegerPayload worker)
    (paperCodingCheckIntegerPayload worker)

private noncomputable def paperVariableAritySyndromeStructuralSourceWordComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperSyndromeStructuralSourceWord worker) :=
  compactPhysicalDecodingFiveFieldComputable
    paperVariableArityCodingCheckCountAtomicComputable
    paperVariableArityCodingBlockLengthAtomicComputable
    paperVariableArityCodingRadiusAtomicComputable
    (paperVariableArityCodingRhsIntegerPayloadComputable worker)
    (paperVariableArityCodingCheckIntegerPayloadComputable worker)

private theorem paperVariableAritySyndromeStructuralSourceWord_valid
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (formula : ThreeCNF) :
    paperSyndromeStructuralSourceWord worker
        (encodeThreeCNF formula) =
      encodeBinarySyndromeDecodingInstance
        (paperVariableAritySyndromeInstance
          (encodeThreeCNF formula).length formula) := by
  unfold paperSyndromeStructuralSourceWord
    compactPhysicalDecodingFiveFieldOutput
  rw [paperVariableArityCodingCheckCountAtomic_valid formula,
    paperVariableArityCodingBlockLengthAtomic_valid formula,
    paperVariableArityCodingRadiusAtomic_valid formula,
    paperVariableArityCodingRhsIntegerPayload_valid worker formula,
    paperVariableArityCodingCheckIntegerPayload_valid worker formula]
  simp only [paperVariableAritySyndromeInstance,
      encodeBinarySyndromeDecodingInstance,
          List.append_assoc]

end PaperBinaryCodingTM

namespace Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal

open GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceConsistencyBridge
open GapCVP.PaperBinaryCodingTM GapCVP.PaperSyndromeInstance
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM

private def paperSyndromeRoutedSourceMap
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (input : List Bool) : List Bool :=
  if constructiveCanonicalSourceMarker input then
    if binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem input then
      paperSyndromeStructuralSourceWord worker input
    else
      encodeBinarySyndromeDecodingInstance canonicalBinarySyndromeNo
  else
    encodeBinarySyndromeDecodingInstance canonicalBinarySyndromeNo

private noncomputable def paperVariableAritySyndromeRoutedSourceComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    BitTM
      (paperSyndromeRoutedSourceMap worker) := by
  have consistency := sourcePreservingConditionalComputable
    (gaussianPaperVariableArityAllInputExactConsistencyComputable worker)
    (paperVariableAritySyndromeStructuralSourceWordComputable worker)
    (encodeBinarySyndromeDecodingInstance canonicalBinarySyndromeNo)
  exact sourcePreservingConditionalComputable
    constructiveCanonicalSourceMarkerComputable
    consistency
    (encodeBinarySyndromeDecodingInstance canonicalBinarySyndromeNo)

private theorem paperVariableAritySyndromeRoutedSource_completeness
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (input : List Bool)
    (membership : paperOriginalThreeSATLanguage input) :
    binarySyndromeDecodingPromise.yes
      (paperSyndromeRoutedSourceMap worker input) := by
  obtain ⟨formula, encoding, satisfiable⟩ :=
    (GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_iff input).mp membership
  subst input
  have consistent :=
    physicalFormulaSystem_consistent_of_satisfiable
      (encodeThreeCNF formula).length formula satisfiable
  have selected : binaryGaussianSourceConsistencyGuard
      paperCanonicalSourceBinarySystem
      (encodeThreeCNF formula) = true := by
    simpa only [binaryGaussianSourceConsistencyGuard, paperCanonicalSourceBinarySystem,
        decodeThreeCNF_encode,
        ↓reduceIte, Core.BinaryAffineSystem.effectiveReducedConsistent_iff, physicalFormulaSystem]
            using consistent
  simpa only [paperSyndromeRoutedSourceMap, constructiveCanonicalSourceMarker,
      decodeThreeCNF_encode,
      decide_true, ↓reduceIte, selected, paperVariableAritySyndromeStructuralSourceWord_valid]
          using
      paperVariableAritySyndromeInstance_completeness (encodeThreeCNF formula).length formula
          satisfiable

private theorem paperVariableAritySyndromeRoutedSource_soundness
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    (input : List Bool)
    (nonmembership : ¬ paperOriginalThreeSATLanguage input) :
    binarySyndromeDecodingPromise.no
      (paperSyndromeRoutedSourceMap worker input) := by
  cases decoded : decodeThreeCNF input with
  | none =>
      simpa only [paperSyndromeRoutedSourceMap, constructiveCanonicalSourceMarker, decoded,
          Bool.false_eq_true,
          ↓reduceIte] using canonicalBinarySyndromeNo_mem
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · subst input
        have unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
            ∀ clause ∈ formula, clauseSatisfied assignment clause := by
          intro satisfiable
          exact nonmembership
            ((GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_iff
              (encodeThreeCNF formula)).mpr ⟨formula, rfl, satisfiable⟩)
        cases consistent :
            (physicalWordBinarySystem
              (encodeThreeCNF formula).length formula).effectiveReducedConsistent with
        | false =>
            simpa only [paperSyndromeRoutedSourceMap, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, ↓reduceIte, binaryGaussianSourceConsistencyGuard,
                    paperCanonicalSourceBinarySystem, consistent,
                Bool.false_eq_true] using canonicalBinarySyndromeNo_mem
        | true =>
            simpa only [paperSyndromeRoutedSourceMap, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, ↓reduceIte, binaryGaussianSourceConsistencyGuard,
                    paperCanonicalSourceBinarySystem, consistent,
                paperVariableAritySyndromeStructuralSourceWord_valid] using
                paperVariableAritySyndromeInstance_soundness (encodeThreeCNF formula).length
                    formula consistent unsatisfiable
      · simpa only [paperSyndromeRoutedSourceMap, constructiveCanonicalSourceMarker, decoded,
          canonical, decide_false,
            Bool.false_eq_true, ↓reduceIte] using canonicalBinarySyndromeNo_mem

private noncomputable def paperVariableAritySyndromeSourceReduction
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer) :
    PromiseReduction paperOriginalThreeSATLanguage
      binarySyndromeDecodingPromise where
  map := paperSyndromeRoutedSourceMap worker
  polynomial_time :=
    ⟨paperVariableAritySyndromeRoutedSourceComputable worker⟩
  completeness := paperVariableAritySyndromeRoutedSource_completeness worker
  soundness := paperVariableAritySyndromeRoutedSource_soundness worker

theorem binarySyndromeDecoding_nphard_unconditional :
    NPHardPromise binarySyndromeDecodingPromise :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    (paperVariableAritySyndromeSourceReduction
      (paperVariableArityCanonicalPhysicalMatrixCellComputer
        paperCanonicalPhysicalMatrixShape))
    polynomialTimeClosedUnderComposition

end Factor400BinaryDecodingPhysicalWordUnconditionalSyndromeFinal

namespace Factor400FinitePNormPromiseReduction

open scoped BigOperators

open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryInstanceBridge

theorem finitePGapFactor_rpow (p : ℚ) (hp : 1 ≤ p)
    (I : GapCVPInstance) :
    finitePGapFactor p I ^ (p : ℝ) =
      binaryCodeGapFactor I.dimension := by
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  unfold finitePGapFactor binaryCodeGapFactor
  rw [← Real.rpow_mul (by exact_mod_cast (Nat.zero_le I.dimension))]
  congr 1
  field_simp

/-- GapCVP reduction support. -/
abbrev finitePCanonicalNoInstance : GapCVPInstance where
  dimension := 1
  basis := !![(2 : ℤ)]
  target _ := 1
  radius := 1 / 2

private theorem finitePCanonicalNoInstance_wellFormed :
    gapCVPWellFormed finitePCanonicalNoInstance := by
  simp only [GapCVP.gapCVPWellFormed, decide_eq_true_eq] at *
  refine ⟨by norm_num [finitePCanonicalNoInstance], ?_,
    by norm_num [finitePCanonicalNoInstance]⟩
  rw [Matrix.det_fin_one_of]
  norm_num

private def finitePCanonicalCoordinate :
    Fin finitePCanonicalNoInstance.dimension :=
  ⟨0, by norm_num [finitePCanonicalNoInstance]⟩

/-- GapCVP reduction support. -/
def finitePCanonicalNoWord : List Bool :=
  (binaryFinEncoding GapCVPInstance).encode finitePCanonicalNoInstance

private theorem finitePCanonicalNo_distance (p : ℚ) (hp : 1 ≤ p)
    (z : Fin finitePCanonicalNoInstance.dimension → ℤ) :
    finitePLatticeDistance p
        finitePCanonicalNoInstance z =
      |(1 : ℝ) - 2 * (z finitePCanonicalCoordinate : ℝ)| := by
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  simpa only [finitePLatticeDistance, finitePNorm,
      finitePCanonicalNoInstance, Fin.sum_univ_one,
      Fin.default_eq_zero, Fin.isValue, finitePLatticeDiscrepancy,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Rat.cast_one, Int.cast_ofNat, abs_nonneg,
      finitePCanonicalCoordinate, Fin.zero_eta] using
      Real.rpow_rpow_inv (abs_nonneg ((1 : ℝ) - 2 * (z finitePCanonicalCoordinate : ℝ)))
          hp_real.ne'

theorem finitePCanonicalNo_mem_no (p : ℚ) (hp : 1 ≤ p) :
    (finitePGapCVPPromise p hp).no
      finitePCanonicalNoWord := by
  simp only [GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise, decide_eq_true_eq]
  refine ⟨finitePCanonicalNoInstance,
    rfl, finitePCanonicalNoInstance_wellFormed, ?_⟩
  intro z
  rw [finitePCanonicalNo_distance p hp z]
  have h := GapCVP.Core.odd_integer_distance_gt_half
    (z finitePCanonicalCoordinate)
  simpa only [finitePGapFactor, finitePCanonicalNoInstance, one_div, Nat.cast_one, mul_inv_rev,
      Real.one_rpow,
      Rat.cast_inv, Rat.cast_ofNat, one_mul, gt_iff_lt] using h

/-- GapCVP reduction support. -/
def effectiveFinitePSignedDiscrepancy
    (H : GapCVP.Core.BinaryAffineSystem)
    (coefficients : Fin H.dimension → ℤ) : Fin H.dimension → ℤ :=
  H.effectiveAffineRepresentative -
    H.effectiveSquareBasisMatrix.mulVec coefficients

theorem effectiveFinitePSignedDiscrepancy_solves
    (H : GapCVP.Core.BinaryAffineSystem)
    (hconsistent : H.effectiveReducedConsistent = true)
    (coefficients : Fin H.dimension → ℤ) :
    H.Solves (effectiveFinitePSignedDiscrepancy H coefficients) := by
  unfold effectiveFinitePSignedDiscrepancy
  apply (GapCVP.Core.effectiveConstructionAInstance_solution_coset
    H hconsistent (H.effectiveSquareBasisMatrix.mulVec coefficients)).mpr
  exact ⟨coefficients, rfl⟩

theorem finitePLatticeDistance_effective_eq_signed_norm
    (p : ℚ) (H : GapCVP.Core.BinaryAffineSystem)
    (hdimension : 0 < H.dimension)
    (radius : ℚ) (hradius : 0 < radius)
    (coefficients : Fin H.dimension → ℤ) :
    finitePLatticeDistance p
        (effectiveGapCVPInstance H hdimension radius hradius)
        coefficients =
      finitePNorm p fun i =>
        (effectiveFinitePSignedDiscrepancy H coefficients i : ℝ) := by
  unfold finitePLatticeDistance
  congr 1
  funext i
  change
    ((H.effectiveAffineRepresentative i : ℚ) : ℝ) -
      (∑ j : Fin H.dimension,
        (H.effectiveSquareBasisMatrix i j : ℝ) *
          (coefficients j : ℝ)) =
      ((H.effectiveAffineRepresentative i -
        (H.effectiveSquareBasisMatrix.mulVec coefficients) i : ℤ) : ℝ)
  simp only [Rat.cast_intCast, Matrix.mulVec, dotProduct, Int.cast_sub, Int.cast_sum, Int.cast_mul]

end Factor400FinitePNormPromiseReduction


end GapCVP

end
