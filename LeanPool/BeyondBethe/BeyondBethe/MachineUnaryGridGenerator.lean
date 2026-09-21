/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeObjectiveSum
import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse

/-!
# A reusable finite-word generator for square rational grids

Given a unary dimension `m`, an explicit accumulator bound, and an immutable
payload, this machine visits the pairs `(0,0),...,(m-1,m-1)` in row-major
order.  A supplied entry machine receives `pair row (pair column payload)`.
Its output is prepended to an encoded-list accumulator.  The explicit `take`
is part of the total machine; clients prove separately that their chosen bound
never truncates a canonical run.

The generator is intentionally independent of the Bethe formulas.  It will be
used both for the nonlinear affine-gradient vector and for complete floor-cut
vectors, avoiding two unrelated implementations of the same grid traversal.
-/

namespace BeyondBethe

open Complexity

def machineUnaryGridGeneratorDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineUnaryGridGeneratorRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineUnaryGridGeneratorInputBound (word : List Bool) : List Bool :=
  machinePairFirst (machineUnaryGridGeneratorRest word)

def machineUnaryGridGeneratorInputPayload (word : List Bool) : List Bool :=
  machinePairSecond (machineUnaryGridGeneratorRest word)

def machineUnaryGridGeneratorPack
    (row column accumulator bound done payload : List Bool) : List Bool :=
  pair row (pair column
    (pair accumulator (pair bound (pair done payload))))

def machineUnaryGridGeneratorRow (state : List Bool) : List Bool :=
  machinePairFirst state

def machineUnaryGridGeneratorColumn (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineUnaryGridGeneratorAccumulator
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineUnaryGridGeneratorBound (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineUnaryGridGeneratorDone (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state))))

def machineUnaryGridGeneratorPayload (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state))))

@[simp] theorem machineUnaryGridGeneratorRow_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorRow
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = row := by
  simp [machineUnaryGridGeneratorRow, machineUnaryGridGeneratorPack]

@[simp] theorem machineUnaryGridGeneratorColumn_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorColumn
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = column := by
  simp [machineUnaryGridGeneratorColumn, machineUnaryGridGeneratorPack]

@[simp] theorem machineUnaryGridGeneratorAccumulator_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorAccumulator
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = accumulator := by
  simp [machineUnaryGridGeneratorAccumulator, machineUnaryGridGeneratorPack]

@[simp] theorem machineUnaryGridGeneratorBound_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorBound
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = bound := by
  simp [machineUnaryGridGeneratorBound, machineUnaryGridGeneratorPack]

@[simp] theorem machineUnaryGridGeneratorDone_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorDone
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = done := by
  simp [machineUnaryGridGeneratorDone, machineUnaryGridGeneratorPack]

@[simp] theorem machineUnaryGridGeneratorPayload_pack
    (row column accumulator bound done payload : List Bool) :
    machineUnaryGridGeneratorPayload
        (machineUnaryGridGeneratorPack row column accumulator bound done payload) = payload := by
  simp [machineUnaryGridGeneratorPayload, machineUnaryGridGeneratorPack]

def machineUnaryGridGeneratorStateDimension
    (state : List Bool) : List Bool :=
  machineUnaryGridGeneratorDimension
    (machineUnaryGridGeneratorPayload state)

def machineUnaryGridGeneratorEntryInput
    (state : List Bool) : List Bool :=
  pair (machineUnaryGridGeneratorRow state)
    (pair (machineUnaryGridGeneratorColumn state)
      (machineUnaryGridGeneratorInputPayload
        (machineUnaryGridGeneratorPayload state)))

def machineUnaryGridGeneratorNextRow (state : List Bool) : List Bool :=
  (machineUnaryGridGeneratorRow state ++ [true]).take
    (machineUnaryGridGeneratorPayload state).length

def machineUnaryGridGeneratorNextColumn (state : List Bool) : List Bool :=
  (machineUnaryGridGeneratorColumn state ++ [true]).take
    (machineUnaryGridGeneratorPayload state).length

def machineUnaryGridGeneratorColumnCompletesBit
    (state : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineUnaryGridGeneratorNextColumn state)
    (machineUnaryGridGeneratorStateDimension state))

def machineUnaryGridGeneratorRowCompletesBit
    (state : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineUnaryGridGeneratorNextRow state)
    (machineUnaryGridGeneratorStateDimension state))

def machineUnaryGridGeneratorCandidate
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  pair (entry (machineUnaryGridGeneratorEntryInput state))
    (machineUnaryGridGeneratorAccumulator state)

def machineUnaryGridGeneratorNextAccumulator
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  (machineUnaryGridGeneratorCandidate entry state).take
    (machineUnaryGridGeneratorBound state).length

def machineUnaryGridGeneratorFinish
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryGridGeneratorPack
    (machineUnaryGridGeneratorRow state)
    (machineUnaryGridGeneratorColumn state)
    (machineUnaryGridGeneratorNextAccumulator entry state)
    (machineUnaryGridGeneratorBound state) [true]
    (machineUnaryGridGeneratorPayload state)

def machineUnaryGridGeneratorAdvanceRow
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryGridGeneratorPack
    (machineUnaryGridGeneratorNextRow state) []
    (machineUnaryGridGeneratorNextAccumulator entry state)
    (machineUnaryGridGeneratorBound state)
    (machineUnaryGridGeneratorDone state)
    (machineUnaryGridGeneratorPayload state)

def machineUnaryGridGeneratorAdvanceColumn
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryGridGeneratorPack
    (machineUnaryGridGeneratorRow state)
    (machineUnaryGridGeneratorNextColumn state)
    (machineUnaryGridGeneratorNextAccumulator entry state)
    (machineUnaryGridGeneratorBound state)
    (machineUnaryGridGeneratorDone state)
    (machineUnaryGridGeneratorPayload state)

def machineUnaryGridGeneratorProcess
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineIfHead (machineUnaryGridGeneratorColumnCompletesBit state)
    (machineIfHead (machineUnaryGridGeneratorRowCompletesBit state)
      (machineUnaryGridGeneratorFinish entry state)
      (machineUnaryGridGeneratorAdvanceRow entry state))
    (machineUnaryGridGeneratorAdvanceColumn entry state)

def machineUnaryGridGeneratorStep
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineUnaryGridGeneratorDone state)) state
    (machineUnaryGridGeneratorProcess entry state)

def machineUnaryGridGeneratorInit (word : List Bool) : List Bool :=
  machineUnaryGridGeneratorPack [] [] []
    (machineUnaryGridGeneratorInputBound word) [false] word

def machineUnaryGridGeneratorDimensionBits
    (word : List Bool) : List Bool :=
  machineLengthBits (machineUnaryGridGeneratorDimension word)

def machineUnaryGridGeneratorWorkBits (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineUnaryGridGeneratorDimensionBits word)
      (machineUnaryGridGeneratorDimensionBits word))

def machineUnaryGridGeneratorGuard (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineUnaryGridGeneratorRuler (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineUnaryGridGeneratorGuard word)
      (machineUnaryGridGeneratorWorkBits word))

def machineUnaryGridGeneratorEnvelope (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2 (word ++ List.replicate 16 false)

def machineUnaryGridGeneratorWidth (word : List Bool) : List Bool :=
  let envelope := machineUnaryGridGeneratorEnvelope word
  machineUnaryGridGeneratorPack envelope envelope envelope envelope
    envelope envelope

def machineUnaryGridGeneratorFinalState
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  (machineUnaryGridGeneratorStep entry)^[(machineUnaryGridGeneratorRuler word).length]
    (machineUnaryGridGeneratorInit word)

def machineUnaryGridGeneratorReversedCode
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineUnaryGridGeneratorAccumulator
    (machineUnaryGridGeneratorFinalState entry word)

def machineUnaryGridGeneratorCode
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineListReverse (machineUnaryGridGeneratorReversedCode entry word)

/-! ## Polynomial-time closure -/

theorem machineUnaryGridGeneratorDimension_mem_FP :
    machineUnaryGridGeneratorDimension ∈ FP := machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorRest_mem_FP :
    machineUnaryGridGeneratorRest ∈ FP := machinePairSecond_mem_FP

theorem machineUnaryGridGeneratorInputBound_mem_FP :
    machineUnaryGridGeneratorInputBound ∈ FP := by
  simpa only [machineUnaryGridGeneratorInputBound] using
    machineCompose_mem_FP machineUnaryGridGeneratorRest_mem_FP
      machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorInputPayload_mem_FP :
    machineUnaryGridGeneratorInputPayload ∈ FP := by
  simpa only [machineUnaryGridGeneratorInputPayload] using
    machineCompose_mem_FP machineUnaryGridGeneratorRest_mem_FP
      machinePairSecond_mem_FP

theorem machineUnaryGridGeneratorRow_mem_FP :
    machineUnaryGridGeneratorRow ∈ FP := machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorColumn_mem_FP :
    machineUnaryGridGeneratorColumn ∈ FP := by
  simpa only [machineUnaryGridGeneratorColumn] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorAccumulator_mem_FP :
    machineUnaryGridGeneratorAccumulator ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineUnaryGridGeneratorAccumulator] using
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorBound_mem_FP :
    machineUnaryGridGeneratorBound ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineUnaryGridGeneratorBound] using
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorDone_mem_FP :
    machineUnaryGridGeneratorDone ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  have htailFour := machineCompose_mem_FP htailThree machinePairSecond_mem_FP
  simpa only [machineUnaryGridGeneratorDone] using
    machineCompose_mem_FP htailFour machinePairFirst_mem_FP

theorem machineUnaryGridGeneratorPayload_mem_FP :
    machineUnaryGridGeneratorPayload ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  have htailFour := machineCompose_mem_FP htailThree machinePairSecond_mem_FP
  simpa only [machineUnaryGridGeneratorPayload] using
    machineCompose_mem_FP htailFour machinePairSecond_mem_FP

theorem machineUnaryGridGeneratorStateDimension_mem_FP :
    machineUnaryGridGeneratorStateDimension ∈ FP := by
  simpa only [machineUnaryGridGeneratorStateDimension] using
    machineCompose_mem_FP machineUnaryGridGeneratorPayload_mem_FP
      machineUnaryGridGeneratorDimension_mem_FP

theorem machineUnaryGridGeneratorEntryInput_mem_FP :
    machineUnaryGridGeneratorEntryInput ∈ FP := by
  have hpayload := machineCompose_mem_FP
    machineUnaryGridGeneratorPayload_mem_FP
    machineUnaryGridGeneratorInputPayload_mem_FP
  exact machinePair_mem_FP machineUnaryGridGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryGridGeneratorColumn_mem_FP hpayload)

theorem machineUnaryGridGeneratorNextRow_mem_FP :
    machineUnaryGridGeneratorNextRow ∈ FP := by
  have happend := machineAppend_mem_FP machineUnaryGridGeneratorRow_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineUnaryGridGeneratorNextRow] using
    machineTake_mem_FP machineUnaryGridGeneratorPayload_mem_FP happend

theorem machineUnaryGridGeneratorNextColumn_mem_FP :
    machineUnaryGridGeneratorNextColumn ∈ FP := by
  have happend := machineAppend_mem_FP machineUnaryGridGeneratorColumn_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineUnaryGridGeneratorNextColumn] using
    machineTake_mem_FP machineUnaryGridGeneratorPayload_mem_FP happend

theorem machineUnaryGridGeneratorColumnCompletesBit_mem_FP :
    machineUnaryGridGeneratorColumnCompletesBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineUnaryGridGeneratorNextColumn_mem_FP
    machineUnaryGridGeneratorStateDimension_mem_FP
  simpa only [machineUnaryGridGeneratorColumnCompletesBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineUnaryGridGeneratorRowCompletesBit_mem_FP :
    machineUnaryGridGeneratorRowCompletesBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineUnaryGridGeneratorNextRow_mem_FP
    machineUnaryGridGeneratorStateDimension_mem_FP
  simpa only [machineUnaryGridGeneratorRowCompletesBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineUnaryGridGeneratorCandidate_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorCandidate entry ∈ FP := by
  have hcurrent := machineCompose_mem_FP
    machineUnaryGridGeneratorEntryInput_mem_FP hentry
  exact machinePair_mem_FP hcurrent
    machineUnaryGridGeneratorAccumulator_mem_FP

theorem machineUnaryGridGeneratorNextAccumulator_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorNextAccumulator entry ∈ FP := by
  simpa only [machineUnaryGridGeneratorNextAccumulator] using
    machineTake_mem_FP machineUnaryGridGeneratorBound_mem_FP
      (machineUnaryGridGeneratorCandidate_mem_FP hentry)

theorem machineUnaryGridGeneratorFinish_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorFinish entry ∈ FP :=
  machinePair_mem_FP machineUnaryGridGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryGridGeneratorColumn_mem_FP
      (machinePair_mem_FP
        (machineUnaryGridGeneratorNextAccumulator_mem_FP hentry)
        (machinePair_mem_FP machineUnaryGridGeneratorBound_mem_FP
          (machinePair_mem_FP (machineConst_mem_FP [true])
            machineUnaryGridGeneratorPayload_mem_FP))))

theorem machineUnaryGridGeneratorAdvanceRow_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorAdvanceRow entry ∈ FP :=
  machinePair_mem_FP machineUnaryGridGeneratorNextRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP
        (machineUnaryGridGeneratorNextAccumulator_mem_FP hentry)
        (machinePair_mem_FP machineUnaryGridGeneratorBound_mem_FP
          (machinePair_mem_FP machineUnaryGridGeneratorDone_mem_FP
            machineUnaryGridGeneratorPayload_mem_FP))))

theorem machineUnaryGridGeneratorAdvanceColumn_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorAdvanceColumn entry ∈ FP :=
  machinePair_mem_FP machineUnaryGridGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryGridGeneratorNextColumn_mem_FP
      (machinePair_mem_FP
        (machineUnaryGridGeneratorNextAccumulator_mem_FP hentry)
        (machinePair_mem_FP machineUnaryGridGeneratorBound_mem_FP
          (machinePair_mem_FP machineUnaryGridGeneratorDone_mem_FP
            machineUnaryGridGeneratorPayload_mem_FP))))

theorem machineUnaryGridGeneratorProcess_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorProcess entry ∈ FP := by
  have hlast := machineIfHead_mem_FP
    machineUnaryGridGeneratorRowCompletesBit_mem_FP
    (machineUnaryGridGeneratorFinish_mem_FP hentry)
    (machineUnaryGridGeneratorAdvanceRow_mem_FP hentry)
  exact machineIfHead_mem_FP
    machineUnaryGridGeneratorColumnCompletesBit_mem_FP hlast
    (machineUnaryGridGeneratorAdvanceColumn_mem_FP hentry)

theorem machineUnaryGridGeneratorStep_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorStep entry ∈ FP := by
  have hdone := machineCompose_mem_FP machineUnaryGridGeneratorDone_mem_FP
    machineHeadBit_mem_FP
  exact machineIfHead_mem_FP hdone id_mem_FP
    (machineUnaryGridGeneratorProcess_mem_FP hentry)

theorem machineUnaryGridGeneratorInit_mem_FP :
    machineUnaryGridGeneratorInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP [])
        (machinePair_mem_FP machineUnaryGridGeneratorInputBound_mem_FP
          (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP))))

theorem machineUnaryGridGeneratorDimensionBits_mem_FP :
    machineUnaryGridGeneratorDimensionBits ∈ FP := by
  simpa only [machineUnaryGridGeneratorDimensionBits] using
    machineCompose_mem_FP machineUnaryGridGeneratorDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineUnaryGridGeneratorWorkBits_mem_FP :
    machineUnaryGridGeneratorWorkBits ∈ FP := by
  have hinput := machinePair_mem_FP
    machineUnaryGridGeneratorDimensionBits_mem_FP
    machineUnaryGridGeneratorDimensionBits_mem_FP
  simpa only [machineUnaryGridGeneratorWorkBits] using
    machineCompose_mem_FP hinput machineBinaryMulBits_mem_FP

theorem machineUnaryGridGeneratorGuard_mem_FP :
    machineUnaryGridGeneratorGuard ∈ FP := machineBinaryMulWidth_mem_FP

theorem machineUnaryGridGeneratorRuler_mem_FP :
    machineUnaryGridGeneratorRuler ∈ FP := by
  have hinput := machinePair_mem_FP machineUnaryGridGeneratorGuard_mem_FP
    machineUnaryGridGeneratorWorkBits_mem_FP
  simpa only [machineUnaryGridGeneratorRuler] using
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineUnaryGridGeneratorEnvelope_mem_FP :
    machineUnaryGridGeneratorEnvelope ∈ FP := by
  have hpadded := machineAppend_mem_FP id_mem_FP
    (machineConst_mem_FP (List.replicate 16 false))
  simpa only [machineUnaryGridGeneratorEnvelope] using
    machineCompose_mem_FP hpadded (machineIteratedBinaryWidth_mem_FP 2)

theorem machineUnaryGridGeneratorWidth_mem_FP :
    machineUnaryGridGeneratorWidth ∈ FP := by
  let h := machineUnaryGridGeneratorEnvelope_mem_FP
  exact machinePair_mem_FP h
    (machinePair_mem_FP h
      (machinePair_mem_FP h
        (machinePair_mem_FP h (machinePair_mem_FP h h))))

def MachineUnaryGridGeneratorStateBound
    (word state : List Bool) : Prop :=
  state = machineUnaryGridGeneratorPack
      (machineUnaryGridGeneratorRow state)
      (machineUnaryGridGeneratorColumn state)
      (machineUnaryGridGeneratorAccumulator state)
      (machineUnaryGridGeneratorBound state)
      (machineUnaryGridGeneratorDone state)
      (machineUnaryGridGeneratorPayload state) ∧
    (machineUnaryGridGeneratorRow state).length ≤ word.length ∧
    (machineUnaryGridGeneratorColumn state).length ≤ word.length ∧
    (machineUnaryGridGeneratorAccumulator state).length ≤
      (machineUnaryGridGeneratorInputBound word).length ∧
    machineUnaryGridGeneratorBound state =
      machineUnaryGridGeneratorInputBound word ∧
    (machineUnaryGridGeneratorDone state).length ≤ 1 ∧
    machineUnaryGridGeneratorPayload state = word

theorem machineUnaryGridGeneratorInit_bound (word : List Bool) :
    MachineUnaryGridGeneratorStateBound word
      (machineUnaryGridGeneratorInit word) := by
  simp [MachineUnaryGridGeneratorStateBound,
    machineUnaryGridGeneratorInit]

theorem machineUnaryGridGeneratorStep_bound
    {entry : List Bool → List Bool} {word state : List Bool}
    (hs : MachineUnaryGridGeneratorStateBound word state) :
    MachineUnaryGridGeneratorStateBound word
      (machineUnaryGridGeneratorStep entry state) := by
  rcases hs with ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩
  have hnextAcc :
      (machineUnaryGridGeneratorNextAccumulator entry state).length ≤
        (machineUnaryGridGeneratorInputBound word).length := by
    rw [machineUnaryGridGeneratorNextAccumulator, hbound]
    exact List.length_take_le _ _
  have hnextRow : (machineUnaryGridGeneratorNextRow state).length ≤
      word.length := by
    rw [machineUnaryGridGeneratorNextRow, hpayload]
    exact List.length_take_le _ _
  have hnextColumn : (machineUnaryGridGeneratorNextColumn state).length ≤
      word.length := by
    rw [machineUnaryGridGeneratorNextColumn, hpayload]
    exact List.length_take_le _ _
  have hfinish : MachineUnaryGridGeneratorStateBound word
      (machineUnaryGridGeneratorFinish entry state) := by
    simp only [MachineUnaryGridGeneratorStateBound,
      machineUnaryGridGeneratorFinish,
      machineUnaryGridGeneratorRow_pack,
      machineUnaryGridGeneratorColumn_pack,
      machineUnaryGridGeneratorAccumulator_pack,
      machineUnaryGridGeneratorBound_pack,
      machineUnaryGridGeneratorDone_pack,
      machineUnaryGridGeneratorPayload_pack]
    exact ⟨trivial, hrow, hcolumn, hnextAcc, hbound, by simp, hpayload⟩
  have hadvanceRow : MachineUnaryGridGeneratorStateBound word
      (machineUnaryGridGeneratorAdvanceRow entry state) := by
    simp only [MachineUnaryGridGeneratorStateBound,
      machineUnaryGridGeneratorAdvanceRow,
      machineUnaryGridGeneratorRow_pack,
      machineUnaryGridGeneratorColumn_pack,
      machineUnaryGridGeneratorAccumulator_pack,
      machineUnaryGridGeneratorBound_pack,
      machineUnaryGridGeneratorDone_pack,
      machineUnaryGridGeneratorPayload_pack]
    exact ⟨trivial, hnextRow, by simp, hnextAcc, hbound, hdone, hpayload⟩
  have hadvanceColumn : MachineUnaryGridGeneratorStateBound word
      (machineUnaryGridGeneratorAdvanceColumn entry state) := by
    simp only [MachineUnaryGridGeneratorStateBound,
      machineUnaryGridGeneratorAdvanceColumn,
      machineUnaryGridGeneratorRow_pack,
      machineUnaryGridGeneratorColumn_pack,
      machineUnaryGridGeneratorAccumulator_pack,
      machineUnaryGridGeneratorBound_pack,
      machineUnaryGridGeneratorDone_pack,
      machineUnaryGridGeneratorPayload_pack]
    exact ⟨trivial, hrow, hnextColumn, hnextAcc, hbound, hdone, hpayload⟩
  rw [machineUnaryGridGeneratorStep]
  cases hdoneCode : machineUnaryGridGeneratorDone state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false,
        machineUnaryGridGeneratorProcess]
      cases hcolumnCode : machineUnaryGridGeneratorColumnCompletesBit state with
      | nil =>
          have hlen :
              (machineUnaryGridGeneratorColumnCompletesBit state).length = 1 := by
            simp [machineUnaryGridGeneratorColumnCompletesBit]
          rw [hcolumnCode] at hlen
          simp at hlen
      | cons columnBit columnTail =>
          cases columnBit with
          | false =>
              rw [machineIfHead_false]
              exact hadvanceColumn
          | true =>
              rw [machineIfHead_true]
              cases hrowCode : machineUnaryGridGeneratorRowCompletesBit state with
              | nil =>
                  have hlen :
                      (machineUnaryGridGeneratorRowCompletesBit state).length = 1 := by
                    simp [machineUnaryGridGeneratorRowCompletesBit]
                  rw [hrowCode] at hlen
                  simp at hlen
              | cons rowBit rowTail =>
                  cases rowBit with
                  | false =>
                      rw [machineIfHead_false]
                      exact hadvanceRow
                  | true =>
                      rw [machineIfHead_true]
                      exact hfinish
  | cons doneBit doneTail =>
      cases doneBit with
      | false =>
          rw [machineHeadBit_cons, machineIfHead_false,
            machineUnaryGridGeneratorProcess]
          cases hcolumnCode : machineUnaryGridGeneratorColumnCompletesBit state with
          | nil =>
              have hlen :
                  (machineUnaryGridGeneratorColumnCompletesBit state).length = 1 := by
                simp [machineUnaryGridGeneratorColumnCompletesBit]
              rw [hcolumnCode] at hlen
              simp at hlen
          | cons columnBit columnTail =>
              cases columnBit with
              | false =>
                  rw [machineIfHead_false]
                  exact hadvanceColumn
              | true =>
                  rw [machineIfHead_true]
                  cases hrowCode : machineUnaryGridGeneratorRowCompletesBit state with
                  | nil =>
                      have hlen :
                          (machineUnaryGridGeneratorRowCompletesBit state).length = 1 := by
                        simp [machineUnaryGridGeneratorRowCompletesBit]
                      rw [hrowCode] at hlen
                      simp at hlen
                  | cons rowBit rowTail =>
                      cases rowBit with
                      | false =>
                          rw [machineIfHead_false]
                          exact hadvanceRow
                      | true =>
                          rw [machineIfHead_true]
                          exact hfinish
      | true =>
          rw [machineHeadBit_cons, machineIfHead_true]
          exact ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩

theorem machineUnaryGridGeneratorIterate_bound
    (entry : List Bool → List Bool) (word : List Bool) : ∀ k,
    MachineUnaryGridGeneratorStateBound word
      ((machineUnaryGridGeneratorStep entry)^[k]
        (machineUnaryGridGeneratorInit word)) := by
  intro k
  induction k with
  | zero => exact machineUnaryGridGeneratorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineUnaryGridGeneratorStep_bound ih

theorem machineUnaryGridGeneratorEnvelope_word_le (word : List Bool) :
    word.length ≤ (machineUnaryGridGeneratorEnvelope word).length := by
  rw [machineUnaryGridGeneratorEnvelope,
    machineIteratedBinaryWidth_length]
  have hpadded : word.length ≤ (word ++ List.replicate 16 false).length := by
    simp
  exact hpadded.trans (certificateExpGuardWidth_self_le 2 _)

theorem machineUnaryGridGeneratorEnvelope_pos (word : List Bool) :
    1 ≤ (machineUnaryGridGeneratorEnvelope word).length := by
  have hword := machineUnaryGridGeneratorEnvelope_word_le word
  by_cases hnil : word = []
  · subst word
    norm_num [machineUnaryGridGeneratorEnvelope,
      machineIteratedBinaryWidth_length, certificateExpGuardWidth]
  · have hpos : 0 < word.length := List.length_pos_of_ne_nil hnil
    have : 1 ≤ word.length := by omega
    omega

theorem machineUnaryGridGeneratorInputBound_le_envelope (word : List Bool) :
    (machineUnaryGridGeneratorInputBound word).length ≤
      (machineUnaryGridGeneratorEnvelope word).length :=
  (machinePairFirst_length_le (machineUnaryGridGeneratorRest word)).trans
    ((machinePairSecond_length_le word).trans
      (machineUnaryGridGeneratorEnvelope_word_le word))

theorem machineUnaryGridGeneratorIterate_length_le_width
    (entry : List Bool → List Bool) (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineUnaryGridGeneratorRuler word).length) :
    ((machineUnaryGridGeneratorStep entry)^[iterations]
      (machineUnaryGridGeneratorInit word)).length ≤
        (machineUnaryGridGeneratorWidth word).length := by
  rcases machineUnaryGridGeneratorIterate_bound entry word iterations with
    ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩
  have hwe := machineUnaryGridGeneratorEnvelope_word_le word
  have hbe := machineUnaryGridGeneratorInputBound_le_envelope word
  have hepos := machineUnaryGridGeneratorEnvelope_pos word
  rw [hdecomp, hbound, hpayload]
  simp only [machineUnaryGridGeneratorPack,
    machineUnaryGridGeneratorWidth, pair_length]
  omega

theorem machineUnaryGridGeneratorFinalState_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorFinalState entry ∈ FP := by
  exact Cobham.iterate_mem_FP
    (machineUnaryGridGeneratorStep_mem_FP hentry)
    machineUnaryGridGeneratorInit_mem_FP
    machineUnaryGridGeneratorRuler_mem_FP
    machineUnaryGridGeneratorWidth_mem_FP
    (machineUnaryGridGeneratorIterate_length_le_width entry)

theorem machineUnaryGridGeneratorReversedCode_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorReversedCode entry ∈ FP := by
  simpa only [machineUnaryGridGeneratorReversedCode] using
    machineCompose_mem_FP
      (machineUnaryGridGeneratorFinalState_mem_FP hentry)
      machineUnaryGridGeneratorAccumulator_mem_FP

theorem machineUnaryGridGeneratorCode_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryGridGeneratorCode entry ∈ FP := by
  simpa only [machineUnaryGridGeneratorCode] using
    machineCompose_mem_FP
      (machineUnaryGridGeneratorReversedCode_mem_FP hentry)
      machineListReverse_mem_FP

/-! ## Canonical inputs and exact iteration ruler -/

def machineUnaryGridGeneratorCanonicalWord
    (m : ℕ) (bound payload : List Bool) : List Bool :=
  pair (List.replicate m true) (pair bound payload)

@[simp] theorem machineUnaryGridGeneratorDimension_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryGridGeneratorDimension
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      List.replicate m true := by
  simp [machineUnaryGridGeneratorDimension,
    machineUnaryGridGeneratorCanonicalWord]

@[simp] theorem machineUnaryGridGeneratorInputBound_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryGridGeneratorInputBound
        (machineUnaryGridGeneratorCanonicalWord m bound payload) = bound := by
  simp [machineUnaryGridGeneratorInputBound,
    machineUnaryGridGeneratorRest,
    machineUnaryGridGeneratorCanonicalWord]

@[simp] theorem machineUnaryGridGeneratorInputPayload_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryGridGeneratorInputPayload
        (machineUnaryGridGeneratorCanonicalWord m bound payload) = payload := by
  simp [machineUnaryGridGeneratorInputPayload,
    machineUnaryGridGeneratorRest,
    machineUnaryGridGeneratorCanonicalWord]

@[simp] theorem machineUnaryGridGeneratorWorkBits_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryGridGeneratorWorkBits
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      (m * m).bits := by
  rw [machineUnaryGridGeneratorWorkBits,
    machineUnaryGridGeneratorDimensionBits,
    machineUnaryGridGeneratorDimension_encode,
    machineLengthBits_encode, List.length_replicate,
    machineBinaryMulBits_pair_natBits]

theorem machineUnaryGridGeneratorWork_le_guard
    (m : ℕ) (bound payload : List Bool) :
    m * m ≤
      (machineUnaryGridGeneratorGuard
        (machineUnaryGridGeneratorCanonicalWord m bound payload)).length := by
  have hm : m ≤
      (machineUnaryGridGeneratorCanonicalWord m bound payload).length := by
    simp only [machineUnaryGridGeneratorCanonicalWord, pair_length,
      List.length_replicate]
    omega
  simp only [machineUnaryGridGeneratorGuard, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

@[simp] theorem machineUnaryGridGeneratorRuler_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryGridGeneratorRuler
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      List.replicate (m * m) true := by
  rw [machineUnaryGridGeneratorRuler,
    machineUnaryGridGeneratorWorkBits_encode,
    machineBoundedUnary_encode_of_le]
  exact machineUnaryGridGeneratorWork_le_guard m bound payload

/-! ## Typed row-major semantics -/

structure UnaryGridSemanticState (m : ℕ) where
  row : Fin m
  column : Fin m
  accumulator : List ℚ
  done : Bool

def unaryGridSemanticInit {m : ℕ} (hm : 0 < m) :
    UnaryGridSemanticState m where
  row := ⟨0, hm⟩
  column := ⟨0, hm⟩
  accumulator := []
  done := false

def unaryGridSemanticStep {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m) :
    UnaryGridSemanticState m :=
  if state.done then state
  else
    let nextAccumulator := f state.row state.column :: state.accumulator
    if hcolumn : state.column.1 + 1 = m then
      if hrow : state.row.1 + 1 = m then
        { state with accumulator := nextAccumulator, done := true }
      else
        { state with
            row := ⟨state.row.1 + 1, by omega⟩
            column := ⟨0, by omega⟩
            accumulator := nextAccumulator }
    else
      { state with
          column := ⟨state.column.1 + 1, by omega⟩
          accumulator := nextAccumulator }

def machineUnaryGridGeneratorSemanticCode {m : ℕ}
    (bound payload : List Bool) (state : UnaryGridSemanticState m) :
    List Bool :=
  machineUnaryGridGeneratorPack
    (List.replicate state.row.1 true)
    (List.replicate state.column.1 true)
    (binaryListCode rationalEntryBinaryCode state.accumulator)
    bound [state.done]
    (machineUnaryGridGeneratorCanonicalWord m bound payload)

@[simp] theorem machineUnaryGridGeneratorEntryInput_semanticCode {m : ℕ}
    (bound payload : List Bool) (state : UnaryGridSemanticState m) :
    machineUnaryGridGeneratorEntryInput
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      pair (List.replicate state.row.1 true)
        (pair (List.replicate state.column.1 true) payload) := by
  simp [machineUnaryGridGeneratorEntryInput,
    machineUnaryGridGeneratorSemanticCode]

@[simp] theorem machineUnaryGridGeneratorNextRow_semanticCode {m : ℕ}
    (bound payload : List Bool) (state : UnaryGridSemanticState m) :
    machineUnaryGridGeneratorNextRow
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      List.replicate (state.row.1 + 1) true := by
  have hlength : state.row.1 + 1 ≤
      (machineUnaryGridGeneratorCanonicalWord m bound payload).length := by
    have hrow : state.row.1 + 1 ≤ m := by omega
    have hm : m ≤
        (machineUnaryGridGeneratorCanonicalWord m bound payload).length := by
      simp only [machineUnaryGridGeneratorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    omega
  rw [machineUnaryGridGeneratorNextRow]
  simp only [machineUnaryGridGeneratorSemanticCode,
    machineUnaryGridGeneratorRow_pack,
    machineUnaryGridGeneratorPayload_pack]
  have happend : List.replicate state.row.1 true ++ [true] =
      List.replicate (state.row.1 + 1) true := by
    rw [show ([true] : List Bool) = List.replicate 1 true by rfl,
      List.replicate_append_replicate]
  rw [happend, List.take_of_length_le (by simpa using hlength)]

@[simp] theorem machineUnaryGridGeneratorNextColumn_semanticCode {m : ℕ}
    (bound payload : List Bool) (state : UnaryGridSemanticState m) :
    machineUnaryGridGeneratorNextColumn
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      List.replicate (state.column.1 + 1) true := by
  have hlength : state.column.1 + 1 ≤
      (machineUnaryGridGeneratorCanonicalWord m bound payload).length := by
    have hcolumn : state.column.1 + 1 ≤ m := by omega
    have hm : m ≤
        (machineUnaryGridGeneratorCanonicalWord m bound payload).length := by
      simp only [machineUnaryGridGeneratorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    omega
  rw [machineUnaryGridGeneratorNextColumn]
  simp only [machineUnaryGridGeneratorSemanticCode,
    machineUnaryGridGeneratorColumn_pack,
    machineUnaryGridGeneratorPayload_pack]
  have happend : List.replicate state.column.1 true ++ [true] =
      List.replicate (state.column.1 + 1) true := by
    rw [show ([true] : List Bool) = List.replicate 1 true by rfl,
      List.replicate_append_replicate]
  rw [happend, List.take_of_length_le (by simpa using hlength)]

@[simp] theorem machineUnaryGridGeneratorColumnCompletesBit_semanticCode
    {m : ℕ} (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryGridGeneratorColumnCompletesBit
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      [decide (state.column.1 + 1 = m)] := by
  rw [machineUnaryGridGeneratorColumnCompletesBit,
    machineUnaryGridGeneratorNextColumn_semanticCode,
    machineUnaryGridGeneratorStateDimension]
  simp only [machineUnaryGridGeneratorSemanticCode,
    machineUnaryGridGeneratorPayload_pack,
    machineUnaryGridGeneratorDimension_encode,
    machineUnaryRulersEqualBit_replicate, machineHeadBit_cons]

@[simp] theorem machineUnaryGridGeneratorRowCompletesBit_semanticCode
    {m : ℕ} (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryGridGeneratorRowCompletesBit
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      [decide (state.row.1 + 1 = m)] := by
  rw [machineUnaryGridGeneratorRowCompletesBit,
    machineUnaryGridGeneratorNextRow_semanticCode,
    machineUnaryGridGeneratorStateDimension]
  simp only [machineUnaryGridGeneratorSemanticCode,
    machineUnaryGridGeneratorPayload_pack,
    machineUnaryGridGeneratorDimension_encode,
    machineUnaryRulersEqualBit_replicate, machineHeadBit_cons]

theorem machineUnaryGridGeneratorStep_semanticCode {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool) (state : UnaryGridSemanticState m)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hlarge :
      (binaryListCode rationalEntryBinaryCode
        (f state.row state.column :: state.accumulator)).length ≤
          bound.length) :
    machineUnaryGridGeneratorStep entry
        (machineUnaryGridGeneratorSemanticCode bound payload state) =
      machineUnaryGridGeneratorSemanticCode bound payload
        (unaryGridSemanticStep f state) := by
  rcases state with ⟨row, column, accumulator, done⟩
  cases done
  · have hcandidate :
        machineUnaryGridGeneratorNextAccumulator entry
            (machineUnaryGridGeneratorSemanticCode bound payload
              ⟨row, column, accumulator, false⟩) =
          binaryListCode rationalEntryBinaryCode
            (f row column :: accumulator) := by
      rw [machineUnaryGridGeneratorNextAccumulator,
        machineUnaryGridGeneratorCandidate,
        machineUnaryGridGeneratorEntryInput_semanticCode,
        hentry]
      simp only [machineUnaryGridGeneratorSemanticCode,
        machineUnaryGridGeneratorAccumulator_pack,
        machineUnaryGridGeneratorBound_pack, binaryListCode]
      exact List.take_of_length_le hlarge
    by_cases hcolumn : column.1 + 1 = m
    · by_cases hrow : row.1 + 1 = m
      · have hdoneFalse :
            machineHeadBit (machineUnaryGridGeneratorDone
              (machineUnaryGridGeneratorSemanticCode bound payload
                ⟨row, column, accumulator, false⟩)) = [false] := by
            simp [machineUnaryGridGeneratorSemanticCode]
        rw [machineUnaryGridGeneratorStep, hdoneFalse,
          machineIfHead_false, machineUnaryGridGeneratorProcess,
          machineUnaryGridGeneratorColumnCompletesBit_semanticCode]
        simp only [hcolumn, decide_true, machineIfHead_true]
        rw [machineUnaryGridGeneratorRowCompletesBit_semanticCode]
        simp only [hrow, decide_true, machineIfHead_true]
        rw [machineUnaryGridGeneratorFinish, hcandidate]
        simp [unaryGridSemanticStep, hcolumn, hrow,
          machineUnaryGridGeneratorSemanticCode]
      · have hdoneFalse :
            machineHeadBit (machineUnaryGridGeneratorDone
              (machineUnaryGridGeneratorSemanticCode bound payload
                ⟨row, column, accumulator, false⟩)) = [false] := by
            simp [machineUnaryGridGeneratorSemanticCode]
        rw [machineUnaryGridGeneratorStep, hdoneFalse,
          machineIfHead_false, machineUnaryGridGeneratorProcess,
          machineUnaryGridGeneratorColumnCompletesBit_semanticCode]
        simp only [hcolumn, decide_true, machineIfHead_true]
        rw [machineUnaryGridGeneratorRowCompletesBit_semanticCode]
        simp only [hrow, decide_false, machineIfHead_false]
        rw [machineUnaryGridGeneratorAdvanceRow,
          machineUnaryGridGeneratorNextRow_semanticCode, hcandidate]
        simp [unaryGridSemanticStep, hcolumn, hrow,
          machineUnaryGridGeneratorSemanticCode]
    · have hdoneFalse :
          machineHeadBit (machineUnaryGridGeneratorDone
            (machineUnaryGridGeneratorSemanticCode bound payload
              ⟨row, column, accumulator, false⟩)) = [false] := by
          simp [machineUnaryGridGeneratorSemanticCode]
      rw [machineUnaryGridGeneratorStep, hdoneFalse,
        machineIfHead_false, machineUnaryGridGeneratorProcess,
        machineUnaryGridGeneratorColumnCompletesBit_semanticCode]
      simp only [hcolumn, decide_false, machineIfHead_false]
      rw [machineUnaryGridGeneratorAdvanceColumn,
        machineUnaryGridGeneratorNextColumn_semanticCode, hcandidate]
      simp [unaryGridSemanticStep, hcolumn,
        machineUnaryGridGeneratorSemanticCode]
  · simp [machineUnaryGridGeneratorStep, unaryGridSemanticStep,
      machineUnaryGridGeneratorSemanticCode]

def unaryGridOrdinal {m : ℕ} (row column : Fin m) : ℕ :=
  row.1 * m + column.1

theorem unaryGridOrdinal_lt_square {m : ℕ}
    (row column : Fin m) : unaryGridOrdinal row column < m * m := by
  rw [unaryGridOrdinal]
  nlinarith [row.isLt, column.isLt]

theorem unaryGridOrdinal_injective (m : ℕ) :
    Function.Injective
      (fun ij : Fin m × Fin m => unaryGridOrdinal ij.1 ij.2) := by
  intro a b hab
  have hmod := congrArg (fun q : ℕ => q % m) hab
  have hmpos : 0 < m := Nat.zero_lt_of_lt a.1.isLt
  have hmodA : unaryGridOrdinal a.1 a.2 % m = a.2.1 := by
    simp [unaryGridOrdinal, Nat.add_mod, Nat.mod_eq_of_lt a.2.isLt,
      hmpos]
  have hmodB : unaryGridOrdinal b.1 b.2 % m = b.2.1 := by
    simp [unaryGridOrdinal, Nat.add_mod, Nat.mod_eq_of_lt b.2.isLt,
      hmpos]
  have hcolumn : a.2.1 = b.2.1 := by
    calc
      a.2.1 = unaryGridOrdinal a.1 a.2 % m := hmodA.symm
      _ = unaryGridOrdinal b.1 b.2 % m := hmod
      _ = b.2.1 := hmodB
  have hrowMul : a.1.1 * m = b.1.1 * m := by
    simp only [unaryGridOrdinal] at hab
    rw [hcolumn] at hab
    exact Nat.add_right_cancel hab
  have hrow : a.1.1 = b.1.1 :=
    Nat.mul_right_cancel hmpos hrowMul
  exact Prod.ext (Fin.ext hrow) (Fin.ext hcolumn)

theorem unaryGridOrdinal_nextColumn {m : ℕ}
    (row column : Fin m) (hcolumn : column.1 + 1 ≠ m) :
    unaryGridOrdinal row
        ⟨column.1 + 1, show column.1 + 1 < m by omega⟩ =
      unaryGridOrdinal row column + 1 := by
  rw [unaryGridOrdinal, unaryGridOrdinal]
  change row.1 * m + (column.1 + 1) =
    row.1 * m + column.1 + 1
  ring

theorem unaryGridOrdinal_nextRow {m : ℕ}
    (row column : Fin m) (hcolumn : column.1 + 1 = m)
    (hrow : row.1 + 1 ≠ m) :
    unaryGridOrdinal
        ⟨row.1 + 1, show row.1 + 1 < m by omega⟩
        ⟨0, show 0 < m by omega⟩ =
      unaryGridOrdinal row column + 1 := by
  rw [unaryGridOrdinal, unaryGridOrdinal]
  change (row.1 + 1) * m + 0 = row.1 * m + column.1 + 1
  calc
    (row.1 + 1) * m + 0 = row.1 * m + m := by ring
    _ = row.1 * m + column.1 + 1 := by omega

theorem unaryGridOrdinal_last {m : ℕ}
    (row column : Fin m) (hcolumn : column.1 + 1 = m)
    (hrow : row.1 + 1 = m) :
    unaryGridOrdinal row column + 1 = m * m := by
  simp [unaryGridOrdinal]
  nlinarith

def unaryGridValues {m : ℕ} (f : Fin m → Fin m → ℚ) : List ℚ :=
  List.ofFn (fun k : Fin (m * m) =>
    f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

def unaryGridPrefix {m : ℕ}
    (f : Fin m → Fin m → ℚ) (k : ℕ) : List ℚ :=
  (unaryGridValues f).take k

@[simp] theorem unaryGridValues_length {m : ℕ}
    (f : Fin m → Fin m → ℚ) : (unaryGridValues f).length = m * m := by
  simp [unaryGridValues]

theorem unaryGridPrefix_succ_of_ordinal {m k : ℕ}
    (f : Fin m → Fin m → ℚ) (row column : Fin m)
    (hordinal : unaryGridOrdinal row column = k) :
    unaryGridPrefix f (k + 1) =
      unaryGridPrefix f k ++ [f row column] := by
  have hk : k < (unaryGridValues f).length := by
    rw [unaryGridValues_length]
    rw [← hordinal]
    exact unaryGridOrdinal_lt_square row column
  have hget : (unaryGridValues f)[k] = f row column := by
    have hk' : k < m * m := by simpa using hk
    let ij : Fin m × Fin m := (row, column)
    have hfin : (⟨k, hk'⟩ : Fin (m * m)) = finProdFinEquiv ij := by
      apply Fin.ext
      change k = column.1 + m * row.1
      calc
        k = row.1 * m + column.1 := hordinal.symm
        _ = column.1 + m * row.1 := by ring
    simp only [unaryGridValues, List.getElem_ofFn]
    rw [hfin, Equiv.symm_apply_apply]
  rw [unaryGridPrefix, unaryGridPrefix]
  simpa only [List.concat_eq_append, hget] using
    (List.take_concat_get hk).symm

def UnaryGridValueInvariant {m : ℕ}
    (f : Fin m → Fin m → ℚ) (k : ℕ)
    (state : UnaryGridSemanticState m) : Prop :=
  (state.done = true ∧ m * m ≤ k ∧
      state.accumulator = (unaryGridValues f).reverse) ∨
  (state.done = false ∧ unaryGridOrdinal state.row state.column = k ∧
      state.accumulator = (unaryGridPrefix f k).reverse)

theorem unaryGridSemanticInit_valueInvariant {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) :
    UnaryGridValueInvariant f 0 (unaryGridSemanticInit hm) := by
  right
  simp [UnaryGridValueInvariant, unaryGridSemanticInit,
    unaryGridOrdinal, unaryGridPrefix]

theorem unaryGridSemanticStep_valueInvariant {m k : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hinvariant : UnaryGridValueInvariant f k state) :
    UnaryGridValueInvariant f (k + 1) (unaryGridSemanticStep f state) := by
  rcases hinvariant with hdone | hactive
  · rcases hdone with ⟨hdone, hwork, haccumulator⟩
    have hstep : unaryGridSemanticStep f state = state := by
      simp [unaryGridSemanticStep, hdone]
    rw [hstep]
    left
    exact ⟨hdone, hwork.trans (by omega), haccumulator⟩
  · rcases hactive with ⟨hdone, hordinal, haccumulator⟩
    have hprefix := unaryGridPrefix_succ_of_ordinal
      f state.row state.column hordinal
    have hnextAccumulator :
        f state.row state.column :: state.accumulator =
          (unaryGridPrefix f (k + 1)).reverse := by
      rw [hprefix, List.reverse_append, haccumulator]
      rfl
    by_cases hcolumn : state.column.1 + 1 = m
    · by_cases hrow : state.row.1 + 1 = m
      · have hstep : unaryGridSemanticStep f state =
            { state with
              accumulator := f state.row state.column :: state.accumulator
              done := true } := by
          simp [unaryGridSemanticStep, hdone, hcolumn, hrow]
        rw [hstep]
        left
        refine ⟨rfl, ?_, ?_⟩
        · have htotal : k + 1 = m * m := by
            rw [← hordinal]
            exact unaryGridOrdinal_last state.row state.column hcolumn hrow
          omega
        · rw [hnextAccumulator]
          have htotal : k + 1 = m * m := by
            rw [← hordinal]
            exact unaryGridOrdinal_last state.row state.column hcolumn hrow
          rw [htotal, unaryGridPrefix,
            List.take_of_length_le (by simp)]
      · have hstep : unaryGridSemanticStep f state =
            { state with
              row := ⟨state.row.1 + 1, by omega⟩
              column := ⟨0, by omega⟩
              accumulator := f state.row state.column :: state.accumulator } := by
          simp [unaryGridSemanticStep, hdone, hcolumn, hrow]
        rw [hstep]
        right
        refine ⟨hdone, ?_, hnextAccumulator⟩
        rw [unaryGridOrdinal_nextRow state.row state.column hcolumn hrow,
          hordinal]
    · have hstep : unaryGridSemanticStep f state =
          { state with
            column := ⟨state.column.1 + 1, by omega⟩
            accumulator := f state.row state.column :: state.accumulator } := by
        simp [unaryGridSemanticStep, hdone, hcolumn]
      rw [hstep]
      right
      refine ⟨hdone, ?_, hnextAccumulator⟩
      rw [unaryGridOrdinal_nextColumn state.row state.column hcolumn,
        hordinal]

def unaryGridSemanticStateAt {m : ℕ} (hm : 0 < m)
    (f : Fin m → Fin m → ℚ) (k : ℕ) : UnaryGridSemanticState m :=
  (unaryGridSemanticStep f)^[k] (unaryGridSemanticInit hm)

theorem unaryGridSemanticStateAt_valueInvariant {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) : ∀ k,
    UnaryGridValueInvariant f k (unaryGridSemanticStateAt hm f k) := by
  intro k
  induction k with
  | zero => exact unaryGridSemanticInit_valueInvariant hm f
  | succ k ih =>
      rw [unaryGridSemanticStateAt, Function.iterate_succ_apply']
      exact unaryGridSemanticStep_valueInvariant f _ ih

theorem unaryGridSemanticStateAt_full_accumulator {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) :
    (unaryGridSemanticStateAt hm f (m * m)).accumulator =
      (unaryGridValues f).reverse := by
  have hinvariant := unaryGridSemanticStateAt_valueInvariant hm f (m * m)
  rcases hinvariant with hdone | hactive
  · exact hdone.2.2
  · have hord := hactive.2.1
    have hlt := unaryGridOrdinal_lt_square
      (unaryGridSemanticStateAt hm f (m * m)).row
      (unaryGridSemanticStateAt hm f (m * m)).column
    omega

theorem unaryGridSemanticStateAt_active {m k : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) (hk : k < m * m) :
    (unaryGridSemanticStateAt hm f k).done = false ∧
      unaryGridOrdinal (unaryGridSemanticStateAt hm f k).row
        (unaryGridSemanticStateAt hm f k).column = k ∧
      (unaryGridSemanticStateAt hm f k).accumulator =
        (unaryGridPrefix f k).reverse := by
  have hinvariant := unaryGridSemanticStateAt_valueInvariant hm f k
  rcases hinvariant with hdone | hactive
  · omega
  · exact hactive

theorem machineUnaryGridGeneratorInit_semanticCode {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool) :
    machineUnaryGridGeneratorInit
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      machineUnaryGridGeneratorSemanticCode bound payload
        (unaryGridSemanticInit hm) := by
  rw [machineUnaryGridGeneratorInit,
    machineUnaryGridGeneratorInputBound_encode]
  simp [
    machineUnaryGridGeneratorSemanticCode, unaryGridSemanticInit,
    machineUnaryGridGeneratorCanonicalWord, binaryListCode]

theorem unaryGridSemanticStateAt_candidate_eq_prefix {m k : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) (hk : k < m * m) :
    f (unaryGridSemanticStateAt hm f k).row
        (unaryGridSemanticStateAt hm f k).column ::
        (unaryGridSemanticStateAt hm f k).accumulator =
      (unaryGridPrefix f (k + 1)).reverse := by
  have hactive := unaryGridSemanticStateAt_active hm f hk
  have hprefix := unaryGridPrefix_succ_of_ordinal f
    (unaryGridSemanticStateAt hm f k).row
    (unaryGridSemanticStateAt hm f k).column hactive.2.1
  rw [hactive.2.2, hprefix, List.reverse_append]
  rfl

theorem machineUnaryGridGeneratorIterate_semanticCode {m : ℕ}
    (hm : 0 < m) (entry : List Bool → List Bool)
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode rationalEntryBinaryCode (unaryGridValues f)).length ≤
        bound.length) :
    ∀ k, k ≤ m * m →
      (machineUnaryGridGeneratorStep entry)^[k]
          (machineUnaryGridGeneratorInit
            (machineUnaryGridGeneratorCanonicalWord m bound payload)) =
        machineUnaryGridGeneratorSemanticCode bound payload
          (unaryGridSemanticStateAt hm f k) := by
  intro k hk
  induction k with
  | zero => exact machineUnaryGridGeneratorInit_semanticCode hm f bound payload
  | succ k ih =>
      have hklt : k < m * m := by omega
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hlarge :
          (binaryListCode rationalEntryBinaryCode
            (f (unaryGridSemanticStateAt hm f k).row
                (unaryGridSemanticStateAt hm f k).column ::
              (unaryGridSemanticStateAt hm f k).accumulator)).length ≤
            bound.length := by
        rw [unaryGridSemanticStateAt_candidate_eq_prefix hm f hklt]
        have hprefixBound := binaryListCode_take_reverse_length_le
          rationalEntryBinaryCode (unaryGridValues f) (k + 1)
        simpa only [unaryGridPrefix] using hprefixBound.trans hbound
      have hstep := machineUnaryGridGeneratorStep_semanticCode entry f
        bound payload (unaryGridSemanticStateAt hm f k) hentry hlarge
      simpa only [unaryGridSemanticStateAt,
        Function.iterate_succ_apply'] using hstep

theorem machineUnaryGridGeneratorReversedCode_encode_of_bound {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode rationalEntryBinaryCode (unaryGridValues f)).length ≤
        bound.length) :
    machineUnaryGridGeneratorReversedCode entry
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      binaryListCode rationalEntryBinaryCode (unaryGridValues f).reverse := by
  cases m with
  | zero =>
      rw [machineUnaryGridGeneratorReversedCode,
        machineUnaryGridGeneratorFinalState,
        machineUnaryGridGeneratorRuler_encode]
      simp [
        machineUnaryGridGeneratorInit,
        machineUnaryGridGeneratorCanonicalWord,
        unaryGridValues, binaryListCode]
  | succ m =>
      have hm : 0 < m + 1 := by omega
      rw [machineUnaryGridGeneratorReversedCode,
        machineUnaryGridGeneratorFinalState,
        machineUnaryGridGeneratorRuler_encode, List.length_replicate,
        machineUnaryGridGeneratorIterate_semanticCode hm entry f bound payload
          hentry hbound ((m + 1) * (m + 1)) le_rfl]
      simp only [machineUnaryGridGeneratorSemanticCode,
        machineUnaryGridGeneratorAccumulator_pack]
      rw [unaryGridSemanticStateAt_full_accumulator hm f]

theorem machineUnaryGridGeneratorCode_encode_of_bound {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode rationalEntryBinaryCode (unaryGridValues f)).length ≤
        bound.length) :
    machineUnaryGridGeneratorCode entry
        (machineUnaryGridGeneratorCanonicalWord m bound payload) =
      binaryListCode rationalEntryBinaryCode (unaryGridValues f) := by
  rw [machineUnaryGridGeneratorCode,
    machineUnaryGridGeneratorReversedCode_encode_of_bound
      entry f bound payload hentry hbound,
    machineListReverse_encode, List.reverse_reverse]

end BeyondBethe
