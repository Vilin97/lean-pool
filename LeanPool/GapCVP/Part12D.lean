/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part12C

/-! # GapCVP proof, part 12, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

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

private def gaussianPhysicalColumnSwappedCheckWord
    (column : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow column)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary column)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary column)

private noncomputable def gaussianPhysicalColumnSwappedCheckComputable
    {column : List Bool → List Bool}
    (hcolumn : BitTM column) :
    BitTM
      (gaussianPhysicalColumnSwappedCheckWord column) :=
  gaussianPhysicalColumnSwappedBitComputable
    (gaussianPhysicalColumnDynamicCheckComputable
      sourceExplicitAffineCellRowComputable hcolumn)
    (gaussianPhysicalColumnDynamicCheckComputable
      gaussianPhysicalColumnNextPivotUnaryComputable hcolumn)
    (gaussianPhysicalColumnDynamicCheckComputable
      gaussianPhysicalColumnCandidateUnaryComputable hcolumn)

private def gaussianPhysicalColumnSwappedRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)

private noncomputable def gaussianPhysicalColumnSwappedRhsComputable :
    BitTM
      gaussianPhysicalColumnSwappedRhsWord :=
  gaussianPhysicalColumnSwappedBitComputable
    (gaussianPhysicalColumnDynamicRhsComputable
      sourceExplicitAffineCellRowComputable
      sourceExplicitAffineCellColumnComputable)
    (gaussianPhysicalColumnDynamicRhsComputable
      gaussianPhysicalColumnNextPivotUnaryComputable
      sourceExplicitAffineCellColumnComputable)
    (gaussianPhysicalColumnDynamicRhsComputable
      gaussianPhysicalColumnCandidateUnaryComputable
      sourceExplicitAffineCellColumnComputable)

private def gaussianPhysicalColumnClearGateWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive)

private noncomputable def gaussianPhysicalColumnClearGateComputable :
    BitTM
      gaussianPhysicalColumnClearGateWord :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      gaussianPhysicalColumnRowIsPivotComputable)
    (gaussianPhysicalColumnSwappedCheckComputable
      gaussianPhysicalColumnCellActiveComputable)

private def gaussianPhysicalColumnCandidateCheckWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicCheckWord
    gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn

private noncomputable def gaussianPhysicalColumnCandidateCheckComputable :
    BitTM
      gaussianPhysicalColumnCandidateCheckWord :=
  gaussianPhysicalColumnDynamicCheckComputable
    gaussianPhysicalColumnCandidateUnaryComputable
    sourceExplicitAffineCellColumnComputable

private def gaussianPhysicalColumnCandidateRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicRhsWord
    gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn

private noncomputable def gaussianPhysicalColumnCandidateRhsComputable :
    BitTM
      gaussianPhysicalColumnCandidateRhsWord :=
  gaussianPhysicalColumnDynamicRhsComputable
    gaussianPhysicalColumnCandidateUnaryComputable
    sourceExplicitAffineCellColumnComputable

private def gaussianPhysicalColumnPivotUpdatedCheckWord : List Bool → List Bool :=
  sourceExplicitAffineXorBits
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord)

private noncomputable def gaussianPhysicalColumnPivotUpdatedCheckComputable :
    BitTM
      gaussianPhysicalColumnPivotUpdatedCheckWord :=
  sourceExplicitAffineXorBitsComputable
    (gaussianPhysicalColumnSwappedCheckComputable
      sourceExplicitAffineCellColumnComputable)
    (fourFamilyBooleanAndComputable
      gaussianPhysicalColumnClearGateComputable
      gaussianPhysicalColumnCandidateCheckComputable)

private def gaussianPhysicalColumnPivotUpdatedRhsWord : List Bool → List Bool :=
  sourceExplicitAffineXorBits gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord)

private noncomputable def gaussianPhysicalColumnPivotUpdatedRhsComputable :
    BitTM
      gaussianPhysicalColumnPivotUpdatedRhsWord :=
  sourceExplicitAffineXorBitsComputable
    gaussianPhysicalColumnSwappedRhsComputable
    (fourFamilyBooleanAndComputable
      gaussianPhysicalColumnClearGateComputable
      gaussianPhysicalColumnCandidateRhsComputable)

private def gaussianPhysicalColumnOriginalCheckWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicCheckWord
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn

private noncomputable def gaussianPhysicalColumnOriginalCheckComputable :
    BitTM
      gaussianPhysicalColumnOriginalCheckWord :=
  gaussianPhysicalColumnDynamicCheckComputable
    sourceExplicitAffineCellRowComputable
    sourceExplicitAffineCellColumnComputable

private def gaussianPhysicalColumnOriginalRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicRhsWord
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn

private noncomputable def gaussianPhysicalColumnOriginalRhsComputable :
    BitTM
      gaussianPhysicalColumnOriginalRhsWord :=
  gaussianPhysicalColumnDynamicRhsComputable
    sourceExplicitAffineCellRowComputable
    sourceExplicitAffineCellColumnComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedCheckWord : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotUpdatedCheckWord
    gaussianPhysicalColumnOriginalCheckWord

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedCheckComputable :
    BitTM
      gaussianPhysicalColumnUpdatedCheckWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotSelectionComputable
    gaussianPhysicalColumnPivotUpdatedCheckComputable
    gaussianPhysicalColumnOriginalCheckComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedRhsWord : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotUpdatedRhsWord
    gaussianPhysicalColumnOriginalRhsWord

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedRhsComputable :
    BitTM
      gaussianPhysicalColumnUpdatedRhsWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotSelectionComputable
    gaussianPhysicalColumnPivotUpdatedRhsComputable
    gaussianPhysicalColumnOriginalRhsComputable

private theorem gaussianPhysicalColumnBinaryAdd_decide
    (first second : ZMod 2) :
    decide (first + second = (1 : ZMod 2)) =
      Bool.xor (decide (first = (1 : ZMod 2)))
        (decide (second = (1 : ZMod 2))) := by
  rcases effectiveBinary_eq_zero_or_one first with hfirst | hfirst <;>
    rcases effectiveBinary_eq_zero_or_one second with hsecond | hsecond <;>
    simp [hfirst, hsecond]

private theorem gaussianPhysicalColumnSwapFormula
    {m : ℕ} (row candidate pivot : Fin m)
    (bit : Fin m → Bool) :
    ((decide (row.val = candidate.val) && bit pivot) ||
      ((decide (row.val = pivot.val) && bit candidate) ||
        (((!decide (row.val = candidate.val)) &&
          (!decide (row.val = pivot.val))) && bit row))) =
      bit (Equiv.swap candidate pivot row) := by
  by_cases hcandidate : row = candidate
  · subst row
    by_cases equal : candidate = pivot
    · subst pivot
      simp only [decide_true, Bool.true_and, Bool.not_true, Bool.and_self, Bool.false_and,
          Bool.or_false,
          Bool.or_self, Equiv.swap_self, Equiv.refl_apply]
    · have different : candidate.val ≠ pivot.val := by
        intro h
        exact equal (Fin.ext h)
      simp only [decide_true, Bool.true_and, different, decide_false, Bool.false_and,
          Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.or_self, Bool.or_false, Equiv.swap_apply_left]
  · have hcandidateVal : row.val ≠ candidate.val := by
      intro equal
      exact hcandidate (Fin.ext equal)
    by_cases hpivot : row = pivot
    · subst row
      simp only [hcandidateVal, decide_false, Bool.false_and, decide_true, Bool.true_and,
          Bool.not_false,
          Bool.not_true, Bool.and_false, Bool.or_false, Bool.false_or, Equiv.swap_apply_right]
    · have hpivotVal : row.val ≠ pivot.val := by
        intro equal
        exact hpivot (Fin.ext equal)
      rw [Equiv.swap_apply_of_ne_of_ne hcandidate hpivot]
      simp only [hcandidateVal, decide_false, Bool.false_and, hpivotVal, Bool.not_false,
          Bool.and_self,
          Bool.true_and, Bool.false_or]

private theorem gaussianPhysicalColumnDecisionWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnDecisionWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      match findPivotOption state active with
      | none => [false]
      | some candidate => true :: List.replicate candidate.val true := by
  have hrows : 0 < m := by
    have hlt := row.isLt
    omega
  unfold gaussianPhysicalColumnDecisionWord
  rw [Function.comp_apply,
    gaussianPhysicalColumnDecisionQuery_query]
  exact gaussianPhysicalPivotDecisionOutput_effective
    state source active hrows

private theorem gaussianPhysicalColumnCandidateUnary_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (candidate : Fin m)
    (found : findPivotOption state active = some candidate) :
    gaussianPhysicalColumnCandidateUnary
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate candidate.val true := by
  unfold gaussianPhysicalColumnCandidateUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnDecisionWord_effective
      state source row column active, found]
  simp only [List.tail_cons]

theorem gaussianPhysicalColumnPivotPresent_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnPivotPresent
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      (findPivotOption state active).isSome := by
  unfold gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotPresentWord
  simp only [Function.comp_apply]
  rw [gaussianPhysicalColumnDecisionWord_effective
    state source row column active]
  cases findPivotOption state active <;> rfl

private theorem gaussianPhysicalColumnRowIsCandidateWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (candidate : Fin m)
    (found : findPivotOption state active = some candidate) :
    gaussianPhysicalColumnRowIsCandidateWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row.val = candidate.val)] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  exact fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCandidateUnary
    input row.val candidate.val
    (gaussianPhysicalColumnCellRow_query row.val column.val active.val
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)

private theorem gaussianPhysicalColumnRowIsPivotWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (pivot : Fin m)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnRowIsPivotWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row.val = pivot.val)] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  apply fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnNextPivotUnary
    input row.val pivot.val
  · exact gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  · simpa only [boundary] using
      gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val

private theorem gaussianPhysicalColumnSwappedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active selected : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val)
    (columnWorker : List Bool → List Bool)
    (selectedWord :
      columnWorker
          (gaussianPhysicalColumnCellQuery
            row.val column.val active.val
            (effectiveGaussianPackedStateWord state source)) =
        List.replicate selected.val true) :
    gaussianPhysicalColumnSwappedCheckWord columnWorker
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((swapRows state.system candidate pivot).check row selected =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have horiginal := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCellRow columnWorker
    row selected hstate
    (gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source))
    selectedWord
  have hnext : gaussianPhysicalColumnNextPivotUnary input =
      List.replicate pivot.val true := by
    simpa only [boundary] using
      (gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val)
  have hpivot := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnNextPivotUnary columnWorker
    pivot selected hstate hnext selectedWord
  have hcandidate := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCandidateUnary columnWorker
    candidate selected hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    selectedWord
  have hrowCandidate :=
    gaussianPhysicalColumnRowIsCandidateWord_effective
      state source row column active candidate found
  have hrowPivot := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hswap := gaussianPhysicalColumnSwappedBitWord_bits
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary columnWorker)
    input (decide (row.val = candidate.val))
    (decide (row.val = pivot.val))
    (decide (state.system.check row selected = (1 : ZMod 2)))
    (decide (state.system.check pivot selected = (1 : ZMod 2)))
    (decide (state.system.check candidate selected = (1 : ZMod 2)))
    hrowCandidate hrowPivot horiginal hpivot hcandidate
  change gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary columnWorker)
    input = _
  rw [hswap]
  exact congrArg (fun bit : Bool => [bit])
    (gaussianPhysicalColumnSwapFormula row candidate pivot
      (fun current =>
        decide (state.system.check current selected = (1 : ZMod 2))))

private theorem gaussianPhysicalColumnSwappedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnSwappedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((swapRows state.system candidate pivot).rhs row =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have horiginal := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCellRow
    gaussianPhysicalColumnCellColumn row column hstate
    (gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source))
    hcolumn
  have hnext : gaussianPhysicalColumnNextPivotUnary input =
      List.replicate pivot.val true := by
    simpa only [boundary] using
      (gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val)
  have hpivot := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnNextPivotUnary
    gaussianPhysicalColumnCellColumn pivot column hstate
    hnext hcolumn
  have hcandidate := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hrowCandidate :=
    gaussianPhysicalColumnRowIsCandidateWord_effective
      state source row column active candidate found
  have hrowPivot := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hswap := gaussianPhysicalColumnSwappedBitWord_bits
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)
    input (decide (row.val = candidate.val))
    (decide (row.val = pivot.val))
    (decide (state.system.rhs row = (1 : ZMod 2)))
    (decide (state.system.rhs pivot = (1 : ZMod 2)))
    (decide (state.system.rhs candidate = (1 : ZMod 2)))
    hrowCandidate hrowPivot horiginal hpivot hcandidate
  change gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)
    input = _
  rw [hswap]
  exact congrArg (fun bit : Bool => [bit])
    (gaussianPhysicalColumnSwapFormula row candidate pivot
      (fun current => decide (state.system.rhs current = (1 : ZMod 2))))

private theorem gaussianPhysicalColumnClearGateWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnClearGateWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row ≠ pivot ∧
        (swapRows state.system candidate pivot).check row active =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hnot := fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnRowIsPivotWord input
    (decide (row.val = pivot.val)) hrow
  have hactive := gaussianPhysicalColumnSwappedCheckWord_effective
    state source row column active active candidate pivot
    found boundary gaussianPhysicalColumnCellActive
    (gaussianPhysicalColumnCellActive_query
      row.val column.val active.val
      (effectiveGaussianPackedStateWord state source))
  have hand := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive)
    input (!(decide (row.val = pivot.val)))
    (decide
      ((swapRows state.system candidate pivot).check row active =
        (1 : ZMod 2))) hnot hactive
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive) input = _
  rw [hand]
  by_cases heq : row = pivot
  · subst row
    simp only [decide_true, Bool.not_true, Bool.false_and, ne_eq, not_true_eq_false, false_and,
        decide_false]
  · have hv : row.val ≠ pivot.val := by
      intro h
      exact heq (Fin.ext h)
    by_cases hbit :
        (swapRows state.system candidate pivot).check row active =
          (1 : ZMod 2) <;>
      simp [heq, hv, hbit]

private theorem gaussianPhysicalColumnPivotUpdatedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnPivotUpdatedCheckWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((clearTargets pivot active (List.finRange m)
          (applyOperation state (.swap candidate pivot))).system.check
            row column = (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  let swapped := swapRows state.system candidate pivot
  let condition := row ≠ pivot ∧
    swapped.check row active = (1 : ZMod 2)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hswapped := gaussianPhysicalColumnSwappedCheckWord_effective
    state source row column active column candidate pivot
    found boundary gaussianPhysicalColumnCellColumn hcolumn
  have hgate := gaussianPhysicalColumnClearGateWord_effective
    state source row column active candidate pivot found boundary
  have hcandidate := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hterm := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnClearGateWord
    gaussianPhysicalColumnCandidateCheckWord input
    (decide condition)
    (decide (state.system.check candidate column = (1 : ZMod 2)))
    hgate hcandidate
  have hxor := sourceExplicitAffineXorBits_valid
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord)
    input
    (decide (swapped.check row column = (1 : ZMod 2)))
    (decide condition &&
      decide (state.system.check candidate column = (1 : ZMod 2)))
    hswapped hterm
  change sourceExplicitAffineXorBits
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord) input = _
  rw [hxor]
  rw [clearTargets_check_finRange]
  change
    [Bool.xor
      (decide (swapped.check row column = (1 : ZMod 2)))
      (decide condition &&
        decide (state.system.check candidate column = (1 : ZMod 2)))] =
      [decide
        ((if condition then
          swapped.check row column + swapped.check pivot column
        else
          swapped.check row column) = (1 : ZMod 2))]
  by_cases hcondition : condition
  · simp only [hcondition, decide_true, Bool.true_and, ite_true]
    rw [gaussianPhysicalColumnBinaryAdd_decide]
    have hpivotEntry : swapped.check pivot column =
        state.system.check candidate column := by
      change state.system.check
        (Equiv.swap candidate pivot pivot) column =
          state.system.check candidate column
      rw [Equiv.swap_apply_right]
    rw [hpivotEntry]
  · simp only [hcondition, decide_false, Bool.false_and, Bool.bne_false, ↓reduceIte]

private theorem gaussianPhysicalColumnPivotUpdatedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnPivotUpdatedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((clearTargets pivot active (List.finRange m)
          (applyOperation state (.swap candidate pivot))).system.rhs
            row = (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  let swapped := swapRows state.system candidate pivot
  let condition := row ≠ pivot ∧
    swapped.check row active = (1 : ZMod 2)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hswapped := gaussianPhysicalColumnSwappedRhsWord_effective
    state source row column active candidate pivot found boundary
  have hgate := gaussianPhysicalColumnClearGateWord_effective
    state source row column active candidate pivot found boundary
  have hcandidate := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hterm := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnClearGateWord
    gaussianPhysicalColumnCandidateRhsWord input
    (decide condition)
    (decide (state.system.rhs candidate = (1 : ZMod 2)))
    hgate hcandidate
  have hxor := sourceExplicitAffineXorBits_valid
    gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord)
    input
    (decide (swapped.rhs row = (1 : ZMod 2)))
    (decide condition &&
      decide (state.system.rhs candidate = (1 : ZMod 2)))
    hswapped hterm
  change sourceExplicitAffineXorBits
    gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord) input = _
  rw [hxor]
  rw [clearTargets_rhs_finRange]
  change
    [Bool.xor
      (decide (swapped.rhs row = (1 : ZMod 2)))
      (decide condition &&
        decide (state.system.rhs candidate = (1 : ZMod 2)))] =
      [decide
        ((if condition then
          swapped.rhs row + swapped.rhs pivot
        else
          swapped.rhs row) = (1 : ZMod 2))]
  by_cases hcondition : condition
  · simp only [hcondition, decide_true, Bool.true_and, ite_true]
    rw [gaussianPhysicalColumnBinaryAdd_decide]
    have hpivotEntry : swapped.rhs pivot =
        state.system.rhs candidate := by
      change state.system.rhs
        (Equiv.swap candidate pivot pivot) =
          state.system.rhs candidate
      rw [Equiv.swap_apply_right]
    rw [hpivotEntry]
  · simp only [hcondition, decide_false, Bool.false_and, Bool.bne_false, ↓reduceIte]

theorem gaussianPhysicalColumnUpdatedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnUpdatedCheckWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide ((columnStep state active).system.check row column =
        (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnCellRow_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  cases found : findPivotOption state active with
  | none =>
      have hpresent : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [found, Option.isSome_none] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      have horiginal := gaussianPhysicalColumnDynamicCheckWord_effective
        state source input gaussianPhysicalColumnCellRow
        gaussianPhysicalColumnCellColumn row column hstate hrow hcolumn
      have hstep : columnStep state active = state := by
        simp only [columnStep, found, dite_eq_ite, ite_self]
      unfold gaussianPhysicalColumnUpdatedCheckWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      change gaussianPhysicalColumnOriginalCheckWord input = _
      rw [hstep]
      exact horiginal
  | some candidate =>
      have habove := (findPivotOption_some state active candidate found).1
      have hactive : state.nextPivot < m := habove.trans_lt candidate.isLt
      let pivot : Fin m := ⟨state.nextPivot, hactive⟩
      have hpresent : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [found, Option.isSome_some] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      unfold gaussianPhysicalColumnUpdatedCheckWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      simp only [↓reduceIte]
      have hupdated := gaussianPhysicalColumnPivotUpdatedCheckWord_effective
        state source row column active candidate pivot found rfl
      simp only [columnStep, hactive, ↓reduceDIte, found]
      exact hupdated

theorem gaussianPhysicalColumnUpdatedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnUpdatedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide ((columnStep state active).system.rhs row =
        (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnCellRow_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  cases found : findPivotOption state active with
  | none =>
      have hpresent : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [found, Option.isSome_none] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      have horiginal := gaussianPhysicalColumnDynamicRhsWord_effective
        state source input gaussianPhysicalColumnCellRow
        gaussianPhysicalColumnCellColumn row column hstate hrow hcolumn
      have hstep : columnStep state active = state := by
        simp only [columnStep, found, dite_eq_ite, ite_self]
      unfold gaussianPhysicalColumnUpdatedRhsWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      change gaussianPhysicalColumnOriginalRhsWord input = _
      rw [hstep]
      exact horiginal
  | some candidate =>
      have habove := (findPivotOption_some state active candidate found).1
      have hactive : state.nextPivot < m := habove.trans_lt candidate.isLt
      let pivot : Fin m := ⟨state.nextPivot, hactive⟩
      have hpresent : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [found, Option.isSome_some] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      unfold gaussianPhysicalColumnUpdatedRhsWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      simp only [↓reduceIte]
      have hupdated := gaussianPhysicalColumnPivotUpdatedRhsWord_effective
        state source row column active candidate pivot found rfl
      simp only [columnStep, hactive, ↓reduceDIte, found]
      exact hupdated

end GaussianAdaptivePhysicalColumnCellUpdateTM

namespace GaussianAdaptivePhysicalColumnStateTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.Factor400BinaryPhysicalWorkers GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnActiveUnary : List Bool → List Bool :=
  firstFieldContents

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnActiveUnaryComputable :
    BitTM
      gaussianPhysicalColumnActiveUnary :=
  firstFieldContentsComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnCurrentState : List Bool → List Bool :=
  firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnCurrentStateComputable :
    BitTM
      gaussianPhysicalColumnCurrentState :=
  firstFieldSuffixComputable

private def gaussianPhysicalColumnOldNextUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalColumnCurrentState

private noncomputable def gaussianPhysicalColumnOldNextUnaryComputable :
    BitTM
      gaussianPhysicalColumnOldNextUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotPresent
    (input : List Bool) : Bool :=
  (gaussianPhysicalPivotDecisionOutput input).headD false

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotPresentComputable :
    BitTM
      (fun input => gaussianPhysicalColumnPivotPresent input :: input) := by
  have hbit := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotDecisionComputable
    binaryGaussianFirstCellComputable
  have hpreserved := originalSourcePreservingComputable hbit
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved factor400KeepFirstDropSecondComputable
  convert hphysical using 1
  funext input
  change gaussianPhysicalColumnPivotPresent input :: input =
    factor400KeepFirstDropSecondWord
      (originalSourcePreservingOutput
        (binaryGaussianFirstCellWord ∘
          gaussianPhysicalPivotDecisionOutput) input)
  cases hpivot : gaussianPhysicalPivotDecisionOutput input with
  | nil =>
      simp only [gaussianPhysicalColumnPivotPresent, hpivot, List.headD_eq_head?_getD,
          List.head?_nil,
          Option.getD_none, factor400KeepFirstDropSecondWord, originalSourcePreservingOutput,
              binaryGaussianFirstCellWord,
          Function.comp_apply, OutputPolynomialCompositionClosure.markerConditionalOutput,
              List.cons_append, List.nil_append,
          List.tail_cons]
  | cons first remaining =>
      simp only [gaussianPhysicalColumnPivotPresent, hpivot, List.headD_eq_head?_getD,
          List.head?_cons,
          Option.getD_some, factor400KeepFirstDropSecondWord, originalSourcePreservingOutput,
              Function.comp_apply,
          binaryGaussianFirstCellWord_valid, List.cons_append, List.nil_append, List.tail_cons]

private def gaussianPhysicalColumnNextSuccessor : List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    gaussianPhysicalColumnOldNextUnary
    (fun _ : List Bool => [true])

private noncomputable def gaussianPhysicalColumnNextSuccessorComputable :
    BitTM
      gaussianPhysicalColumnNextSuccessor :=
  fourFamilyComputedUnarySumComputable
    gaussianPhysicalColumnOldNextUnaryComputable
    (sourceFixedWordComputable [true])

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnNextPivotUnary : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnNextSuccessor
    gaussianPhysicalColumnOldNextUnary

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnNextPivotUnaryComputable :
    BitTM
      gaussianPhysicalColumnNextPivotUnary :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotPresentComputable
    gaussianPhysicalColumnNextSuccessorComputable
    gaussianPhysicalColumnOldNextUnaryComputable

@[simp] theorem gaussianPhysicalColumnActiveUnary_query
    (column : ℕ) (state : List Bool) :
    gaussianPhysicalColumnActiveUnary
        (gaussianPhysicalPivotColumnQuery column state) =
      List.replicate column true := by
  simp only [gaussianPhysicalColumnActiveUnary, gaussianPhysicalPivotColumnQuery,
      firstFieldContents_valid]

@[simp] theorem gaussianPhysicalColumnCurrentState_query
    (column : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCurrentState
        (gaussianPhysicalPivotColumnQuery column state) = state := by
  simp only [gaussianPhysicalColumnCurrentState, gaussianPhysicalPivotColumnQuery,
      firstFieldSuffix_valid]

@[simp] private theorem gaussianPhysicalColumnOldNextUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPhysicalColumnOldNextUnary
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalColumnOldNextUnary, gaussianPhysicalColumnCurrentState,
      gaussianPhysicalPivotColumnQuery, effectiveGaussianPackedStateWord, List.append_assoc,
          Function.comp_apply,
      firstFieldSuffix_valid, firstFieldContents_valid]

theorem gaussianPhysicalColumnPivotPresent_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnPivotPresent
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      (findPivotOption state column).isSome := by
  unfold gaussianPhysicalColumnPivotPresent
  rw [gaussianPhysicalPivotDecisionOutput_effective
    state source column hrows]
  cases findPivotOption state column <;> rfl

private theorem gaussianPhysicalColumnNextSuccessor_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPhysicalColumnNextSuccessor
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (state.nextPivot + 1) true := by
  apply fourFamilyComputedUnarySumOutput_valid
    gaussianPhysicalColumnOldNextUnary
    (fun _ : List Bool => [true])
    (gaussianPhysicalPivotColumnQuery column.val
      (effectiveGaussianPackedStateWord state source))
    state.nextPivot 1
  · exact gaussianPhysicalColumnOldNextUnary_effective
      state source column
  · rfl

private theorem gaussianPhysicalColumn_foundPivot_next_lt
    {m n : ℕ} (state : State m n)
    (column : Fin n) (row : Fin m)
    (hfound : findPivotOption state column = some row) :
    state.nextPivot < m := by
  have hle := (findPivotOption_some state column row hfound).1
  exact lt_of_le_of_lt hle row.isLt

theorem gaussianPhysicalColumnNextPivotUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnNextPivotUnary
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (columnStep state column).nextPivot true := by
  let input := gaussianPhysicalPivotColumnQuery column.val
    (effectiveGaussianPackedStateWord state source)
  have hmarker := gaussianPhysicalColumnPivotPresent_effective
    state source column hrows
  change gaussianPhysicalColumnNextPivotUnary input = _
  unfold gaussianPhysicalColumnNextPivotUnary
    binaryGaussianDynamicBranchOutput
  cases hfound : findPivotOption state column with
  | none =>
      have hfalse : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [hfound, Option.isSome_none] using hmarker
      rw [hfalse, ite_eq_right Bool.false_ne_true]
      rw [gaussianPhysicalColumnOldNextUnary_effective]
      by_cases hactive : state.nextPivot < m <;>
        simp [columnStep, hactive, hfound]
  | some row =>
      have htrue : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [hfound, Option.isSome_some] using hmarker
      have hactive : state.nextPivot < m :=
        gaussianPhysicalColumn_foundPivot_next_lt
          state column row hfound
      rw [htrue, ite_eq_left rfl]
      rw [gaussianPhysicalColumnNextSuccessor_effective]
      simp only [columnStep, hactive, ↓reduceDIte, hfound, clearTargets_pivots]

private theorem effectiveGaussianColumnStepPivotWord
    {m n : ℕ} (state : State m n)
    (active column : Fin n) :
    effectiveGaussianStatePivotWord
        (columnStep state active) column =
      if (findPivotOption state active).isSome &&
          decide (active = column) then
        true :: List.replicate state.nextPivot true
      else
        effectiveGaussianStatePivotWord state column := by
  cases hfound : findPivotOption state active with
  | none =>
      by_cases hactive : state.nextPivot < m <;>
        simp [columnStep, hactive, hfound]
  | some row =>
      have hactive : state.nextPivot < m :=
        gaussianPhysicalColumn_foundPivot_next_lt
          state active row hfound
      by_cases heq : active = column
      · subst column
        simp only [effectiveGaussianStatePivotWord,
            effectiveGaussianStatePivotRowOption, columnStep,
            hactive, ↓reduceDIte,
            hfound, applyOperation, clearTargets_pivots, decide_true, List.find?_cons_of_pos,
                Option.map_some,
            Option.isSome_some, Bool.and_self, ↓reduceIte]
      · simp only [effectiveGaussianStatePivotWord,
          effectiveGaussianStatePivotRowOption, columnStep,
          hactive, ↓reduceDIte,
            hfound, applyOperation, clearTargets_pivots, heq, decide_false, Bool.false_eq_true,
                not_false_eq_true,
            List.find?_cons_of_neg, Option.isSome_some, Bool.and_false, ↓reduceIte]

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotRecordOuter :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotRecordOuterComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordOuter :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable

@[simp] theorem gaussianPhysicalColumnPivotRecordOuter_word
    (rank width active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnPivotRecordOuter
        (gaussianPhysicalPivotRecordWord rank width active state) =
      gaussianPhysicalPivotColumnQuery active state := by
  simp only [gaussianPhysicalColumnPivotRecordOuter, gaussianPhysicalPivotRecordWord,
      List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid]

private def gaussianPhysicalColumnOldPivotQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
    (lengthPrefixedWord [] ++
      gaussianPhysicalPivotRecordState input)

private noncomputable def gaussianPhysicalColumnOldPivotQueryComputable :
    BitTM
      gaussianPhysicalColumnOldPivotQuery := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordRowComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hzero
      gaussianPhysicalPivotRecordStateComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalPivotRecordState input))
  simpa only [Function.comp_apply] using hphysical

@[simp] private theorem gaussianPhysicalColumnOldPivotQuery_word
    (rank width active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnOldPivotQuery
        (gaussianPhysicalPivotRecordWord rank width active state) =
      affineCellQuery rank 0 state := by
  simp only [gaussianPhysicalColumnOldPivotQuery, gaussianPhysicalPivotRecordRow_word,
      gaussianPhysicalPivotRecordState_word, affineCellQuery, List.replicate_zero,
          List.append_assoc]

private def gaussianPhysicalColumnOldPivotWord : List Bool → List Bool :=
  gaussianPackedStatePivotCellWord ∘
    gaussianPhysicalColumnOldPivotQuery

private noncomputable def gaussianPhysicalColumnOldPivotComputable :
    BitTM
      gaussianPhysicalColumnOldPivotWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnOldPivotQueryComputable
    gaussianPackedStatePivotCellComputable

private theorem gaussianPhysicalColumnOldPivotWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) :
    gaussianPhysicalColumnOldPivotWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state column := by
  unfold gaussianPhysicalColumnOldPivotWord
  rw [Function.comp_apply,
    gaussianPhysicalColumnOldPivotQuery_word]
  exact gaussianPackedStatePivotCellWord_query
    state source column

private def gaussianPhysicalColumnPivotRecordActiveEq :
    List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn

private noncomputable def gaussianPhysicalColumnPivotRecordActiveEqComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordActiveEq :=
  fourFamilyComputedUnaryEqBitComputable
    gaussianPhysicalPivotRecordRowComputable
    gaussianPhysicalPivotRecordColumnComputable

private def gaussianPhysicalColumnPivotRecordPresentWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    gaussianPhysicalPivotDecisionOutput ∘
    gaussianPhysicalColumnPivotRecordOuter

private noncomputable def gaussianPhysicalColumnPivotRecordPresentComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordPresentWord := by
  have hdecision := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnPivotRecordOuterComputable
    gaussianPhysicalPivotDecisionComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hdecision binaryGaussianFirstCellComputable

private def gaussianPhysicalColumnPivotRecordUpdateMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPhysicalColumnPivotRecordPresentWord
    gaussianPhysicalColumnPivotRecordActiveEq

private noncomputable def gaussianPhysicalColumnPivotRecordUpdateMarkerComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordUpdateMarker :=
  fourFamilyBooleanAndComputable
    gaussianPhysicalColumnPivotRecordPresentComputable
    gaussianPhysicalColumnPivotRecordActiveEqComputable

private def gaussianPhysicalColumnNewPivotWord
    (input : List Bool) : List Bool :=
  [true] ++ gaussianPhysicalPivotRecordNextUnary input

private noncomputable def gaussianPhysicalColumnNewPivotComputable :
    BitTM
      gaussianPhysicalColumnNewPivotWord :=
  pointwiseAppendComputable
    (sourceFixedWordComputable [true])
    gaussianPhysicalPivotRecordNextUnaryComputable

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalComputedMarkerPreservingComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker) :
    BitTM
      (fun input => (marker input).headD false :: input) := by
  have hbit := GapCVP.TMComposition.computableInPolyTime
    computer binaryGaussianFirstCellComputable
  have hpreserved := originalSourcePreservingComputable hbit
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved factor400KeepFirstDropSecondComputable
  convert hphysical using 1
  funext input
  change (marker input).headD false :: input =
    factor400KeepFirstDropSecondWord
      (originalSourcePreservingOutput
        (binaryGaussianFirstCellWord ∘ marker) input)
  cases hmarker : marker input with
  | nil =>
      simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
          factor400KeepFirstDropSecondWord,
          originalSourcePreservingOutput, binaryGaussianFirstCellWord, Function.comp_apply,
          OutputPolynomialCompositionClosure.markerConditionalOutput, hmarker, List.cons_append,
              List.nil_append,
          List.tail_cons]
  | cons bit remaining =>
      simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
          factor400KeepFirstDropSecondWord,
          originalSourcePreservingOutput, Function.comp_apply, hmarker,
              binaryGaussianFirstCellWord_valid, List.cons_append,
          List.nil_append, List.tail_cons]

private def gaussianPhysicalColumnPivotRecordShouldUpdate
    (input : List Bool) : Bool :=
  (gaussianPhysicalColumnPivotRecordUpdateMarker input).headD false

private noncomputable def gaussianPhysicalColumnPivotRecordShouldUpdateComputable :
    BitTM
      (fun input =>
        gaussianPhysicalColumnPivotRecordShouldUpdate input :: input) :=
  gaussianPhysicalComputedMarkerPreservingComputable
    gaussianPhysicalColumnPivotRecordUpdateMarkerComputable

private def gaussianPhysicalColumnUpdatedPivotWord :
    List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotRecordShouldUpdate
    gaussianPhysicalColumnNewPivotWord
    gaussianPhysicalColumnOldPivotWord

private noncomputable def gaussianPhysicalColumnUpdatedPivotComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotRecordShouldUpdateComputable
    gaussianPhysicalColumnNewPivotComputable
    gaussianPhysicalColumnOldPivotComputable

private theorem gaussianPhysicalColumnPivotRecordActiveEq_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) :
    gaussianPhysicalColumnPivotRecordActiveEq
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (column = active)] := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have heq := fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn input
    column.val active.val
    (gaussianPhysicalPivotRecordRow_word
      column.val width active.val
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalPivotRecordColumn_word
      column.val width active.val
      (effectiveGaussianPackedStateWord state source))
  change gaussianPhysicalColumnPivotRecordActiveEq input = _
  change fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn input = _
  rw [heq]
  by_cases h : column = active
  · subst active
    simp only [decide_true]
  · have hv : column.val ≠ active.val := by
      intro hv
      exact h (Fin.ext hv)
    simp only [hv, decide_false, h]

private theorem gaussianPhysicalColumnPivotRecordPresentWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnPivotRecordPresentWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [(findPivotOption state active).isSome] := by
  unfold gaussianPhysicalColumnPivotRecordPresentWord
  simp only [Function.comp_apply,
    gaussianPhysicalColumnPivotRecordOuter_word]
  rw [gaussianPhysicalPivotDecisionOutput_effective
    state source active hrows]
  cases findPivotOption state active <;>
    simp [binaryGaussianFirstCellWord,
      GapCVP.OutputPolynomialCompositionClosure.markerConditionalOutput]

private theorem gaussianPhysicalColumnPivotRecordUpdateMarker_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnPivotRecordUpdateMarker
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [(findPivotOption state active).isSome &&
        decide (column = active)] := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have hpresent := gaussianPhysicalColumnPivotRecordPresentWord_effective
    state source column active width hrows
  have hequal := gaussianPhysicalColumnPivotRecordActiveEq_effective
    state source column active width
  exact fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnPivotRecordPresentWord
    gaussianPhysicalColumnPivotRecordActiveEq input
    (findPivotOption state active).isSome
    (decide (column = active)) hpresent hequal

private theorem gaussianPhysicalColumnUpdatedPivotWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord
        (columnStep state active) column := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have hmarker := gaussianPhysicalColumnPivotRecordUpdateMarker_effective
    state source column active width hrows
  have hnext := gaussianPhysicalPivotRecordNextUnary_word
    state source column.val width active.val
  have hold := gaussianPhysicalColumnOldPivotWord_effective
    state source column active width
  have hsemantic := effectiveGaussianColumnStepPivotWord
    state active column
  change gaussianPhysicalColumnUpdatedPivotWord input = _
  unfold gaussianPhysicalColumnUpdatedPivotWord
    binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotRecordShouldUpdate
  rw [hmarker]
  cases hfound : findPivotOption state active with
  | none =>
      simp only [Option.isSome_none, Bool.false_and,
        List.headD_cons, Bool.false_eq_true, ↓reduceIte]
      rw [hold, hsemantic, hfound]
      simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | some row =>
      by_cases heq : column = active
      · subst column
        simp only [Option.isSome_some, decide_true,
          Bool.and_self, List.headD_cons, ↓reduceIte]
        change [true] ++
          gaussianPhysicalPivotRecordNextUnary input = _
        rw [hnext, hsemantic, hfound]
        simp only [List.cons_append, List.nil_append, Option.isSome_some, decide_true,
            Bool.and_self, ↓reduceIte]
      · have hreverse : active ≠ column := Ne.symm heq
        simp only [Option.isSome_some, heq, decide_false,
          Bool.and_false, List.headD_cons,
          Bool.false_eq_true, ↓reduceIte]
        rw [hold, hsemantic, hfound]
        simp only [Option.isSome_some, hreverse, decide_false, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte]

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotWidthOutput : List Bool → List Bool :=
  gaussianDenseStateDimensionUnary ∘
    gaussianPhysicalColumnCurrentState

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotWidthComputable :
    BitTM
      gaussianPhysicalColumnPivotWidthOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    gaussianDenseStateDimensionUnaryComputable

private noncomputable def gaussianPhysicalColumnPivotWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalColumnPivotWidthOutput
  computer := gaussianPhysicalColumnPivotWidthComputable

private def gaussianPhysicalColumnUpdatedPivotRecordOutput :
    List Bool → List Bool :=
  (fun word => lengthPrefixedWord word) ∘
    gaussianPhysicalColumnUpdatedPivotWord

private noncomputable def gaussianPhysicalColumnUpdatedPivotRecordComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnUpdatedPivotComputable
    structuralPrefixWriterComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedPivotCatalogueOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedPivotCatalogueComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotCatalogueOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable

theorem gaussianPhysicalColumnPivotWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnPivotWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate n true := by
  change gaussianDenseStateDimensionUnary
    (gaussianPhysicalColumnCurrentState
      (gaussianPhysicalPivotColumnQuery active.val
        (effectiveGaussianPackedStateWord state source))) = _
  rw [gaussianPhysicalColumnCurrentState_query]
  exact gaussianDenseStateDimensionUnary_effective
    state source hrows

private theorem gaussianPhysicalColumnUpdatedPivotCatalogueOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalColumnPivotWidth.output input =
      List.replicate count true) :
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalColumnUpdatedPivotRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalColumnPivotWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable
    input count hwidth

private theorem gaussianPhysicalColumnPivotGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank : ℕ) (hrows : 0 < m) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalColumnPivotWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord rank n active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalColumnPivotWidth_effective
    state source active hrows]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]

private theorem gaussianPhysicalColumnUpdatedPivotRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotRecordOutput
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      lengthPrefixedWord
        (effectiveGaussianStatePivotWord
          (columnStep state active) column) := by
  unfold gaussianPhysicalColumnUpdatedPivotRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalColumnUpdatedPivotWord_effective
      state source column active width hrows]

theorem gaussianPhysicalColumnUpdatedPivotCatalogueOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedPivotCatalogue
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalColumnPivotWidth.output input =
      List.replicate n true :=
    gaussianPhysicalColumnPivotWidth_effective
      state source active hrows
  have hcatalogue :=
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput_valid
      input n hwidth
  calc
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput input =
        (List.range n).flatMap (fun rank =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalColumnPivotWidth input)) :=
      hcatalogue
    _ = (List.range n).flatMap (fun rank =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (gaussianPhysicalPivotRecordWord rank n active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalColumnUpdatedPivotRecordOutput
        (gaussianPhysicalColumnPivotGeneratedRecord_effective
          state source active rank hrows)
    _ = (List.finRange n).flatMap (fun column =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (gaussianPhysicalPivotRecordWord column.val n active.val
              (effectiveGaussianPackedStateWord state source))) :=
      gaussianPhysicalPivot_range_flatMap_finRange n _
    _ = (List.finRange n).flatMap (fun column =>
          lengthPrefixedWord
            (effectiveGaussianStatePivotWord
              (columnStep state active) column)) := by
      apply List.flatMap_congr
      intro column _
      exact gaussianPhysicalColumnUpdatedPivotRecordOutput_effective
        state source column active n hrows
    _ = effectiveGaussianPackedPivotCatalogue
          (columnStep state active) := by
      unfold effectiveGaussianPackedPivotCatalogue
        binaryGaussianPivotBatchStream
        sourceMixedRadixOriginalSourceQueryStream
      rw [List.flatMap_map]

end GaussianAdaptivePhysicalColumnStateTM


end GapCVP

end
