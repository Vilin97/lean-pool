/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineKuhnInvariant
import Mathlib.Tactic

/-!
# A complete finite-word perfect-matching runner

This file constructs the initial Kuhn state directly from a rational-matrix
word and iterates the verified transition for the length of its fixed octic
envelope.  All definitions are total on malformed words; the correctness
theorems concern canonical matrix encodings.
-/

namespace BeyondBethe

open Complexity

/-! ## Initializer -/

def machineKuhnInitDimension (matrix : List Bool) : List Bool :=
  machineMatrixDimensionUnary matrix

def machineKuhnInitColumns (matrix : List Bool) : List Bool :=
  machineUnaryRangeCode (machineKuhnInitDimension matrix)

def machineKuhnInitFalseSeen (matrix : List Bool) : List Bool :=
  machineFalseVectorCode (machineKuhnInitDimension matrix)

def machineKuhnInitEmptyMate (matrix : List Bool) : List Bool :=
  machineEmptyMateVectorCode (machineKuhnInitDimension matrix)

def machineKuhnInitBuildFrame (matrix : List Bool) : List Bool :=
  pair [true]
    (machineKuhnBuildFramePack (machineListTail (machineKuhnInitColumns matrix))
      (machineKuhnInitEmptyMate matrix))

def machineKuhnInitStack (matrix : List Bool) : List Bool :=
  machineKuhnStackPush (machineKuhnInitBuildFrame matrix) []

def machineKuhnInitNonemptyControl (matrix : List Bool) : List Bool :=
  machineKuhnControlCall (true :: machineKuhnInitDimension matrix)
    (machineKuhnInitColumns matrix)
    (machineListHead (machineKuhnInitColumns matrix))
    (machineKuhnInitFalseSeen matrix) (machineKuhnInitEmptyMate matrix)
    (machineKuhnInitStack matrix)

def machineKuhnInitControl (matrix : List Bool) : List Bool :=
  machineIfEmpty (machineKuhnInitDimension matrix)
    (machineKuhnControlDone (machineKuhnInitEmptyMate matrix))
    (machineKuhnInitNonemptyControl matrix)

def machineKuhnInputClamp (matrix candidate : List Bool) : List Bool :=
  candidate.take (machineKuhnInputBound matrix).length

def machineKuhnInit (matrix : List Bool) : List Bool :=
  machineKuhnStatePack
    (machineKuhnInputClamp matrix (machineKuhnInitControl matrix))
    (machineKuhnInputClamp matrix matrix)
    (machineKuhnInputClamp matrix (machineKuhnInitDimension matrix))
    (machineKuhnInputClamp matrix (machineKuhnInitColumns matrix))
    (machineKuhnInputClamp matrix (machineKuhnInitFalseSeen matrix))
    (machineKuhnInputBound matrix)

theorem machineKuhnInitDimension_mem_FP :
    machineKuhnInitDimension ∈ Complexity.FP :=
  machineMatrixDimensionUnary_mem_FP

theorem machineKuhnInitColumns_mem_FP :
    machineKuhnInitColumns ∈ Complexity.FP := by
  simpa only [machineKuhnInitColumns] using!
    machineCompose_mem_FP machineKuhnInitDimension_mem_FP
      machineUnaryRangeCode_mem_FP

theorem machineKuhnInitFalseSeen_mem_FP :
    machineKuhnInitFalseSeen ∈ Complexity.FP := by
  simpa only [machineKuhnInitFalseSeen] using!
    machineCompose_mem_FP machineKuhnInitDimension_mem_FP
      machineFalseVectorCode_mem_FP

theorem machineKuhnInitEmptyMate_mem_FP :
    machineKuhnInitEmptyMate ∈ Complexity.FP := by
  simpa only [machineKuhnInitEmptyMate] using!
    machineCompose_mem_FP machineKuhnInitDimension_mem_FP
      machineEmptyMateVectorCode_mem_FP

theorem machineKuhnInitBuildFrame_mem_FP :
    machineKuhnInitBuildFrame ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineKuhnInitColumns_mem_FP
    machineListTail_mem_FP
  have hpayload := machinePair_mem_FP htail machineKuhnInitEmptyMate_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true]) hpayload

theorem machineKuhnInitStack_mem_FP :
    machineKuhnInitStack ∈ Complexity.FP := by
  exact machinePair_mem_FP machineKuhnInitBuildFrame_mem_FP
    (machineConst_mem_FP [])

theorem machineKuhnInitNonemptyControl_mem_FP :
    machineKuhnInitNonemptyControl ∈ Complexity.FP := by
  have hfuel := machineCompose_mem_FP machineKuhnInitDimension_mem_FP
    (machinePrepend_mem_FP true)
  have hrow := machineCompose_mem_FP machineKuhnInitColumns_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP hfuel
      (machinePair_mem_FP machineKuhnInitColumns_mem_FP
        (machinePair_mem_FP hrow
          (machinePair_mem_FP machineKuhnInitFalseSeen_mem_FP
            (machinePair_mem_FP machineKuhnInitEmptyMate_mem_FP
              machineKuhnInitStack_mem_FP)))))

theorem machineKuhnInitControl_mem_FP :
    machineKuhnInitControl ∈ Complexity.FP := by
  have hdone := machinePair_mem_FP (machineConst_mem_FP [true, true])
    machineKuhnInitEmptyMate_mem_FP
  exact machineIfEmpty_mem_FP machineKuhnInitDimension_mem_FP hdone
    machineKuhnInitNonemptyControl_mem_FP

theorem machineKuhnInputBound_mem_FP :
    machineKuhnInputBound ∈ Complexity.FP := by
  simpa only [machineKuhnInputBound] using!
    machineCompose_mem_FP machineListUpdateInputBound_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineKuhnInputClamp_mem_FP
    {candidate : List Bool → List Bool} (hcandidate : candidate ∈ Complexity.FP) :
    (fun matrix ↦ machineKuhnInputClamp matrix (candidate matrix)) ∈
      Complexity.FP := by
  simpa only [machineKuhnInputClamp] using!
    machineTake_mem_FP machineKuhnInputBound_mem_FP hcandidate

theorem machineKuhnInit_mem_FP : machineKuhnInit ∈ Complexity.FP := by
  exact machinePair_mem_FP
    (machineKuhnInputClamp_mem_FP machineKuhnInitControl_mem_FP)
    (machinePair_mem_FP (machineKuhnInputClamp_mem_FP id_mem_FP)
      (machinePair_mem_FP
        (machineKuhnInputClamp_mem_FP machineKuhnInitDimension_mem_FP)
        (machinePair_mem_FP
          (machineKuhnInputClamp_mem_FP machineKuhnInitColumns_mem_FP)
          (machinePair_mem_FP
            (machineKuhnInputClamp_mem_FP machineKuhnInitFalseSeen_mem_FP)
            machineKuhnInputBound_mem_FP))))

/-! ## Generic length bounds needed by bounded iteration -/

theorem machineKuhnInitDimension_length_le (matrix : List Bool) :
    (machineKuhnInitDimension matrix).length ≤ matrix.length := by
  let word := pair matrix (machineMatrixDimensionWord matrix)
  have hbound := machineBoundedUnaryIterate_bound word matrix.length
  rcases hbound with ⟨_hpack, _hremaining, hacc⟩
  change (machineBoundedUnaryAcc
      ((machineBoundedUnaryStep)^[matrix.length]
        (machineBoundedUnaryInit word))).length ≤ matrix.length at hacc
  simpa [machineKuhnInitDimension, machineMatrixDimensionUnary,
    machineBoundedUnary, machineBoundedUnaryFinalState,
    machineBoundedUnaryRuler, word] using! hacc

theorem machineUnaryRangeCode_length_le_inputBound (ruler : List Bool) :
    (machineUnaryRangeCode ruler).length ≤
      (machineUnaryRangeInputBound ruler).length := by
  have hbound := machineUnaryRangeIterate_bound ruler ruler.length
  dsimp only [MachineUnaryRangeStateBound] at hbound
  rcases hbound with ⟨_hpack, _hremaining, hacc, _hbound⟩
  simpa [machineUnaryRangeCode, machineUnaryRangeFinalState] using! hacc

@[simp] theorem machineFalseVectorCode_length (ruler : List Bool) :
    (machineFalseVectorCode ruler).length = 4 * ruler.length := by
  rw [machineFalseVectorCode, machineFalseVectorIterate_semantics]
  simp

@[simp] theorem machineEmptyMateVectorCode_length (ruler : List Bool) :
    (machineEmptyMateVectorCode ruler).length = 4 * ruler.length := by
  simp [machineEmptyMateVectorCode]

theorem machineListUpdateInputBound_length_le_kuhnBound
    (matrix : List Bool) :
    (machineListUpdateInputBound matrix).length ≤
      (machineKuhnInputBound matrix).length := by
  simp only [machineKuhnInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineKuhn_matrix_length_le_bound (matrix : List Bool) :
    matrix.length ≤ (machineKuhnInputBound matrix).length := by
  exact (machineListUpdate_word_length_le_bound matrix).trans
    (machineListUpdateInputBound_length_le_kuhnBound matrix)

theorem machineKuhnInitColumns_length_le_bound (matrix : List Bool) :
    (machineKuhnInitColumns matrix).length ≤
      (machineKuhnInputBound matrix).length := by
  have hdimension := machineKuhnInitDimension_length_le matrix
  have hrange := machineUnaryRangeCode_length_le_inputBound
    (machineKuhnInitDimension matrix)
  have hmono := machineListUpdateInputBound_length_mono hdimension
  exact hrange.trans <| hmono.trans <|
    machineListUpdateInputBound_length_le_kuhnBound matrix

theorem machineKuhnInitColumns_length_le_base (matrix : List Bool) :
    (machineKuhnInitColumns matrix).length ≤
      (machineListUpdateInputBound matrix).length := by
  have hdimension := machineKuhnInitDimension_length_le matrix
  exact (machineUnaryRangeCode_length_le_inputBound
      (machineKuhnInitDimension matrix)).trans
    (machineListUpdateInputBound_length_mono hdimension)

theorem machineKuhnInitFalseSeen_length_le_bound (matrix : List Bool) :
    (machineKuhnInitFalseSeen matrix).length ≤
      (machineKuhnInputBound matrix).length := by
  rw [machineKuhnInitFalseSeen, machineFalseVectorCode_length]
  have hdimension := machineKuhnInitDimension_length_le matrix
  have hlinear : 4 * matrix.length ≤
      (machineKuhnInputBound matrix).length := by
    simp only [machineKuhnInputBound, machineListUpdateInputBound,
      machineBinaryMulWidth, List.length_replicate, List.length_append]
    ring_nf
    omega
  exact (Nat.mul_le_mul_left 4 hdimension).trans hlinear

theorem machineKuhnInitEmptyMate_length_le_bound (matrix : List Bool) :
    (machineKuhnInitEmptyMate matrix).length ≤
      (machineKuhnInputBound matrix).length := by
  simpa [machineKuhnInitEmptyMate, machineKuhnInitFalseSeen,
    machineEmptyMateVectorCode] using!
      machineKuhnInitFalseSeen_length_le_bound matrix

/-! ## A generic invariant for the outer bounded iteration -/

def MachineKuhnRunStateBound (matrix state : List Bool) : Prop :=
  let B := (machineKuhnInputBound matrix).length
  state = machineKuhnStatePack (machineKuhnStateControl state)
      (machineKuhnStateMatrix state) (machineKuhnStateDimension state)
      (machineKuhnStateColumns state) (machineKuhnStateFalseSeen state)
      (machineKuhnStateBound state) ∧
    (machineKuhnStateControl state).length ≤ B ∧
    (machineKuhnStateMatrix state).length ≤ B ∧
    (machineKuhnStateDimension state).length ≤ B ∧
    (machineKuhnStateColumns state).length ≤ B ∧
    (machineKuhnStateFalseSeen state).length ≤ B ∧
    machineKuhnStateBound state = machineKuhnInputBound matrix

theorem machineKuhnInit_bound (matrix : List Bool) :
    MachineKuhnRunStateBound matrix (machineKuhnInit matrix) := by
  dsimp only [MachineKuhnRunStateBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [machineKuhnInit]
  · simp [machineKuhnInit, machineKuhnInputClamp]
  · simp [machineKuhnInit, machineKuhnInputClamp]
  · simp [machineKuhnInit, machineKuhnInputClamp]
  · simp [machineKuhnInit, machineKuhnInputClamp]
  · simp [machineKuhnInit, machineKuhnInputClamp]
  · simp [machineKuhnInit]

theorem machineKuhnStep_bound {matrix state : List Bool}
    (hstate : MachineKuhnRunStateBound matrix state) :
    MachineKuhnRunStateBound matrix (machineKuhnStep state) := by
  dsimp only [MachineKuhnRunStateBound] at hstate ⊢
  rcases hstate with
    ⟨hpack, hcontrol, hmatrix, hdimension, hcolumns, hfalse, hbound⟩
  rw [machineKuhnStep, machineKuhnWithControl]
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [machineKuhnStateControl_pack, machineKuhnClamp,
      List.length_take, hbound]
    exact Nat.min_le_left _ _
  · simp only [machineKuhnStateMatrix_pack, machineKuhnClamp,
      List.length_take, hbound]
    exact Nat.min_le_left _ _
  · simp only [machineKuhnStateDimension_pack, machineKuhnClamp,
      List.length_take, hbound]
    exact Nat.min_le_left _ _
  · simp only [machineKuhnStateColumns_pack, machineKuhnClamp,
      List.length_take, hbound]
    exact Nat.min_le_left _ _
  · simp only [machineKuhnStateFalseSeen_pack, machineKuhnClamp,
      List.length_take, hbound]
    exact Nat.min_le_left _ _
  · simp [hbound]

theorem machineKuhnIterate_bound (matrix : List Bool) : ∀ iterations,
    MachineKuhnRunStateBound matrix
      ((machineKuhnStep^[iterations]) (machineKuhnInit matrix)) := by
  intro iterations
  induction iterations with
  | zero => simpa using! machineKuhnInit_bound matrix
  | succ iterations ih =>
      rw [Function.iterate_succ_apply']
      exact machineKuhnStep_bound ih

def machineKuhnRunWidth (matrix : List Bool) : List Bool :=
  machineBinaryMulWidth (machineKuhnInputBound matrix)

theorem machineKuhnRunWidth_mem_FP :
    machineKuhnRunWidth ∈ Complexity.FP := by
  simpa only [machineKuhnRunWidth] using!
    machineCompose_mem_FP machineKuhnInputBound_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineKuhnIterate_length_le_width
    (matrix : List Bool) (iterations : ℕ)
    (_hiterations : iterations ≤ (machineKuhnInputBound matrix).length) :
    ((machineKuhnStep^[iterations]) (machineKuhnInit matrix)).length ≤
      (machineKuhnRunWidth matrix).length := by
  have hstate := machineKuhnIterate_bound matrix iterations
  dsimp only [MachineKuhnRunStateBound] at hstate
  rcases hstate with
    ⟨hpack, hcontrol, hmatrix, hdimension, hcolumns, hfalse, hbound⟩
  rw [hpack]
  simp only [machineKuhnStatePack, pair_length]
  have hlinear :
      2 * (machineKuhnStateControl
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length + 2 +
        2 * (machineKuhnStateMatrix
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length + 2 +
        2 * (machineKuhnStateDimension
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length + 2 +
        2 * (machineKuhnStateColumns
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length + 2 +
        2 * (machineKuhnStateFalseSeen
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length + 2 +
        (machineKuhnStateBound
          ((machineKuhnStep^[iterations]) (machineKuhnInit matrix))).length ≤
      11 * (machineKuhnInputBound matrix).length + 10 := by
    rw [hbound]
    omega
  have hwidth : 11 * (machineKuhnInputBound matrix).length + 10 ≤
      (machineKuhnRunWidth matrix).length := by
    simp only [machineKuhnRunWidth, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
    nlinarith
  omega

def machineKuhnFinalState (matrix : List Bool) : List Bool :=
  (machineKuhnStep^[(machineKuhnInputBound matrix).length])
    (machineKuhnInit matrix)

theorem machineKuhnFinalState_mem_FP :
    machineKuhnFinalState ∈ Complexity.FP := by
  simpa only [machineKuhnFinalState] using!
    Cobham.iterate_mem_FP machineKuhnStep_mem_FP machineKuhnInit_mem_FP
      machineKuhnInputBound_mem_FP machineKuhnRunWidth_mem_FP
      machineKuhnIterate_length_le_width

/-! ## Exact semantics on canonical matrix words -/

@[simp] theorem columnMateList_emptyColumnMate (n : ℕ) :
    columnMateList (emptyColumnMate n) = List.replicate n none := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    simp [columnMateList, emptyColumnMate]

@[simp] theorem machineKuhnInitDimension_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInitDimension
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate n true := by
  exact machineMatrixDimensionUnary_encode A

@[simp] theorem machineKuhnInitColumns_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInitColumns
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      finRangeUnaryCode n := by
  simp [machineKuhnInitColumns]

@[simp] theorem machineKuhnInitFalseSeen_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInitFalseSeen
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      boolVectorCode (List.replicate n false) := by
  simp [machineKuhnInitFalseSeen]

@[simp] theorem machineKuhnInitEmptyMate_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInitEmptyMate
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      mateVectorCode (columnMateList (emptyColumnMate n)) := by
  simp [machineKuhnInitEmptyMate]

theorem machineKuhnInitControl_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInitControl
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      kuhnControlCode
        (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) := by
  cases n with
  | zero =>
      simp [machineKuhnInitControl, machineKuhnInitNonemptyControl,
        kuhnBuildEvalState, kuhnControlCode, finRangeUnaryCode,
        finListUnaryCode, binaryListCode]
  | succ n =>
      simp [machineKuhnInitControl, machineKuhnInitNonemptyControl,
        machineKuhnInitStack, machineKuhnInitBuildFrame,
        kuhnBuildEvalState, kuhnControlCode, kuhnStackCode,
        kuhnFrameCode, kuhnBuildFrameCode, finRangeUnaryCode,
        finListUnaryCode, binaryListCode, machineKuhnStackPush,
        List.finRange_succ, machineListHead, machineListTail,
        finUnaryCode, List.replicate_succ]

theorem machineKuhnInputClamp_eq (matrix candidate : List Bool)
    (hcandidate : candidate.length ≤ (machineKuhnInputBound matrix).length) :
    machineKuhnInputClamp matrix candidate = candidate := by
  exact List.take_of_length_le hcandidate

@[simp] theorem machineKuhnInit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnInit (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      kuhnMachineStateCode A
        (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) := by
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let initial := kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)
  have hinitial := kuhnFullBuildEvalState_reachableBound A
  have hcontrol : (machineKuhnInitControl matrix).length ≤
      (machineKuhnInputBound matrix).length := by
    rw [machineKuhnInitControl_encode]
    exact kuhnControlCode_length_le_inputBound A initial hinitial
      (Nat.zero_le _)
  rw [machineKuhnInit]
  rw [machineKuhnInputClamp_eq matrix _ hcontrol]
  rw [machineKuhnInputClamp_eq matrix _
    (kuhnMatrixCode_length_le_inputBound A)]
  simp only [machineKuhnInitDimension_encode,
    machineKuhnInitColumns_encode, machineKuhnInitFalseSeen_encode]
  rw [machineKuhnInputClamp_eq matrix _
    (kuhnDimensionCode_length_le_inputBound A)]
  rw [machineKuhnInputClamp_eq matrix _
    (kuhnColumnsCode_length_le_inputBound A)]
  rw [machineKuhnInputClamp_eq matrix _
    (kuhnFalseSeenCode_length_le_inputBound A)]
  simp [kuhnMachineStateCode, machineKuhnInitControl_encode,
    matrix, initial]

@[simp] theorem machineKuhnFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnFinalState
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      kuhnMachineStateCode A (.done (kuhnColumnMate A)) := by
  rw [machineKuhnFinalState, machineKuhnInit_encode]
  exact machineKuhnFullBoundIterate_encode A

end BeyondBethe
