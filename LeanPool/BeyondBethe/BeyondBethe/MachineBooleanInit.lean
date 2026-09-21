/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBooleanMemory

/-!
# Polynomially bounded Boolean storage initialization

The matching machine needs all-false vectors and square Boolean matrices.
Both constructors use unary dimension rulers.  Their state is clamped by a
quadratic word computed from the original input; the exact semantic bounds
show that this clamp is inactive on canonical dimension rulers.
-/

namespace BeyondBethe

open Complexity

/-! ## False vectors -/

def machineFalseVectorStep (acc : List Bool) : List Bool :=
  pair [false] acc

def machineFalseVectorWidth (ruler : List Bool) : List Bool :=
  machineBinaryMulWidth ruler

def machineFalseVectorCode (ruler : List Bool) : List Bool :=
  (machineFalseVectorStep)^[ruler.length] []

theorem machineFalseVectorStep_mem_FP :
    machineFalseVectorStep ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP

theorem machineFalseVectorWidth_mem_FP :
    machineFalseVectorWidth ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineFalseVectorIterate_semantics : ∀ k,
    (machineFalseVectorStep)^[k] [] =
      boolVectorCode (List.replicate k false) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineFalseVectorStep, boolVectorCode, binaryListCode,
        boolElementCode, List.replicate_succ]

theorem machineFalseVectorIterate_length_le_width
    (ruler : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ ruler.length) :
    ((machineFalseVectorStep)^[iterations] []).length ≤
      (machineFalseVectorWidth ruler).length := by
  rw [machineFalseVectorIterate_semantics]
  simp only [boolVectorCode, binaryListCode_length_eq_sum,
    List.map_replicate, List.sum_replicate, boolElementCode,
    List.length_singleton, machineFalseVectorWidth,
    machineBinaryMulWidth, List.length_replicate, List.length_append,
    Nat.nsmul_eq_mul]
  nlinarith

theorem machineFalseVectorCode_mem_FP :
    machineFalseVectorCode ∈ Complexity.FP := by
  simpa only [machineFalseVectorCode] using
    Cobham.iterate_mem_FP machineFalseVectorStep_mem_FP
      (machineConst_mem_FP []) id_mem_FP machineFalseVectorWidth_mem_FP
      machineFalseVectorIterate_length_le_width

@[simp] theorem machineFalseVectorCode_encode (n : ℕ) :
    machineFalseVectorCode (List.replicate n true) =
      boolVectorCode (List.replicate n false) := by
  rw [machineFalseVectorCode, List.length_replicate,
    machineFalseVectorIterate_semantics]

/-! ## Repeated-row matrices -/

def machineRepeatedRowMatrixRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRepeatedRowMatrixRow (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRepeatedRowMatrixBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineRepeatedRowMatrixPack
    (row acc bound : List Bool) : List Bool :=
  pair row (pair acc bound)

def machineRepeatedRowMatrixStateRow (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRepeatedRowMatrixStateAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRepeatedRowMatrixStateBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineRepeatedRowMatrixCandidate (state : List Bool) : List Bool :=
  pair (machineRepeatedRowMatrixStateRow state)
    (machineRepeatedRowMatrixStateAcc state)

def machineRepeatedRowMatrixNextAcc (state : List Bool) : List Bool :=
  (machineRepeatedRowMatrixCandidate state).take
    (machineRepeatedRowMatrixStateBound state).length

def machineRepeatedRowMatrixStep (state : List Bool) : List Bool :=
  machineRepeatedRowMatrixPack (machineRepeatedRowMatrixStateRow state)
    (machineRepeatedRowMatrixNextAcc state)
    (machineRepeatedRowMatrixStateBound state)

def machineRepeatedRowMatrixInit (word : List Bool) : List Bool :=
  machineRepeatedRowMatrixPack (machineRepeatedRowMatrixRow word) []
    (machineRepeatedRowMatrixBound word)

def machineRepeatedRowMatrixWidth (word : List Bool) : List Bool :=
  machineRepeatedRowMatrixPack (machineRepeatedRowMatrixBound word)
    (machineRepeatedRowMatrixBound word)
    (machineRepeatedRowMatrixBound word)

def machineRepeatedRowMatrixFinalState (word : List Bool) : List Bool :=
  (machineRepeatedRowMatrixStep)^[(machineRepeatedRowMatrixRuler word).length]
    (machineRepeatedRowMatrixInit word)

def machineRepeatedRowMatrixCode (word : List Bool) : List Bool :=
  machineRepeatedRowMatrixStateAcc
    (machineRepeatedRowMatrixFinalState word)

theorem machineRepeatedRowMatrixRuler_mem_FP :
    machineRepeatedRowMatrixRuler ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRepeatedRowMatrixRow_mem_FP :
    machineRepeatedRowMatrixRow ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineRepeatedRowMatrixBound_mem_FP :
    machineRepeatedRowMatrixBound ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineRepeatedRowMatrixStateRow_mem_FP :
    machineRepeatedRowMatrixStateRow ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRepeatedRowMatrixStateAcc_mem_FP :
    machineRepeatedRowMatrixStateAcc ∈ Complexity.FP := by
  simpa only [machineRepeatedRowMatrixStateAcc] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRepeatedRowMatrixStateBound_mem_FP :
    machineRepeatedRowMatrixStateBound ∈ Complexity.FP := by
  simpa only [machineRepeatedRowMatrixStateBound] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineRepeatedRowMatrixCandidate_mem_FP :
    machineRepeatedRowMatrixCandidate ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRepeatedRowMatrixStateRow_mem_FP
    machineRepeatedRowMatrixStateAcc_mem_FP

theorem machineRepeatedRowMatrixNextAcc_mem_FP :
    machineRepeatedRowMatrixNextAcc ∈ Complexity.FP := by
  simpa only [machineRepeatedRowMatrixNextAcc] using
    machineTake_mem_FP machineRepeatedRowMatrixStateBound_mem_FP
      machineRepeatedRowMatrixCandidate_mem_FP

theorem machineRepeatedRowMatrixStep_mem_FP :
    machineRepeatedRowMatrixStep ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRepeatedRowMatrixStateRow_mem_FP
    (machinePair_mem_FP machineRepeatedRowMatrixNextAcc_mem_FP
      machineRepeatedRowMatrixStateBound_mem_FP)

theorem machineRepeatedRowMatrixInit_mem_FP :
    machineRepeatedRowMatrixInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRepeatedRowMatrixRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      machineRepeatedRowMatrixBound_mem_FP)

theorem machineRepeatedRowMatrixWidth_mem_FP :
    machineRepeatedRowMatrixWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRepeatedRowMatrixBound_mem_FP
    (machinePair_mem_FP machineRepeatedRowMatrixBound_mem_FP
      machineRepeatedRowMatrixBound_mem_FP)

@[simp] theorem machineRepeatedRowMatrixStateRow_pack (a b c) :
    machineRepeatedRowMatrixStateRow
      (machineRepeatedRowMatrixPack a b c) = a := by
  simp [machineRepeatedRowMatrixStateRow, machineRepeatedRowMatrixPack]

@[simp] theorem machineRepeatedRowMatrixStateAcc_pack (a b c) :
    machineRepeatedRowMatrixStateAcc
      (machineRepeatedRowMatrixPack a b c) = b := by
  simp [machineRepeatedRowMatrixStateAcc, machineRepeatedRowMatrixPack]

@[simp] theorem machineRepeatedRowMatrixStateBound_pack (a b c) :
    machineRepeatedRowMatrixStateBound
      (machineRepeatedRowMatrixPack a b c) = c := by
  simp [machineRepeatedRowMatrixStateBound, machineRepeatedRowMatrixPack]

def MachineRepeatedRowMatrixStateBound
    (word state : List Bool) : Prop :=
  let B := (machineRepeatedRowMatrixBound word).length
  state = machineRepeatedRowMatrixPack
      (machineRepeatedRowMatrixStateRow state)
      (machineRepeatedRowMatrixStateAcc state)
      (machineRepeatedRowMatrixStateBound state) ∧
    (machineRepeatedRowMatrixStateRow state).length ≤ B ∧
    (machineRepeatedRowMatrixStateAcc state).length ≤ B ∧
    (machineRepeatedRowMatrixStateBound state).length ≤ B

theorem machineRepeatedRowMatrix_word_length_le_bound (word : List Bool) :
    word.length ≤ (machineRepeatedRowMatrixBound word).length := by
  simp only [machineRepeatedRowMatrixBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineRepeatedRowMatrixInit_bound (word : List Bool) :
    MachineRepeatedRowMatrixStateBound word
      (machineRepeatedRowMatrixInit word) := by
  simp only [MachineRepeatedRowMatrixStateBound,
    machineRepeatedRowMatrixInit,
    machineRepeatedRowMatrixStateRow_pack,
    machineRepeatedRowMatrixStateAcc_pack,
    machineRepeatedRowMatrixStateBound_pack]
  refine ⟨trivial, ?_, by simp, le_rfl⟩
  exact (machinePairSecond_length_le word).trans
    (machineRepeatedRowMatrix_word_length_le_bound word)

theorem machineRepeatedRowMatrixStep_bound
    {word state : List Bool}
    (hstate : MachineRepeatedRowMatrixStateBound word state) :
    MachineRepeatedRowMatrixStateBound word
      (machineRepeatedRowMatrixStep state) := by
  dsimp only [MachineRepeatedRowMatrixStateBound] at hstate ⊢
  rcases hstate with ⟨_, hrow, _hacc, hbound⟩
  simp only [machineRepeatedRowMatrixStep,
    machineRepeatedRowMatrixStateRow_pack,
    machineRepeatedRowMatrixStateAcc_pack,
    machineRepeatedRowMatrixStateBound_pack]
  refine ⟨trivial, hrow, ?_, hbound⟩
  exact (List.length_take_le _ _).trans hbound

theorem machineRepeatedRowMatrixIterate_bound (word : List Bool) : ∀ k,
    MachineRepeatedRowMatrixStateBound word
      ((machineRepeatedRowMatrixStep)^[k]
        (machineRepeatedRowMatrixInit word)) := by
  intro k
  induction k with
  | zero => exact machineRepeatedRowMatrixInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRepeatedRowMatrixStep_bound ih

theorem machineRepeatedRowMatrixIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineRepeatedRowMatrixRuler word).length) :
    ((machineRepeatedRowMatrixStep)^[iterations]
      (machineRepeatedRowMatrixInit word)).length ≤
        (machineRepeatedRowMatrixWidth word).length := by
  rcases machineRepeatedRowMatrixIterate_bound word iterations with
    ⟨hdecomp, hrow, hacc, hbound⟩
  rw [hdecomp]
  simp only [machineRepeatedRowMatrixPack,
    machineRepeatedRowMatrixWidth, pair_length]
  omega

theorem machineRepeatedRowMatrixFinalState_mem_FP :
    machineRepeatedRowMatrixFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineRepeatedRowMatrixStep_mem_FP
    machineRepeatedRowMatrixInit_mem_FP
    machineRepeatedRowMatrixRuler_mem_FP
    machineRepeatedRowMatrixWidth_mem_FP
    machineRepeatedRowMatrixIterate_length_le_width

theorem machineRepeatedRowMatrixCode_mem_FP :
    machineRepeatedRowMatrixCode ∈ Complexity.FP := by
  simpa only [machineRepeatedRowMatrixCode] using
    machineCompose_mem_FP machineRepeatedRowMatrixFinalState_mem_FP
      machineRepeatedRowMatrixStateAcc_mem_FP

/-! ## Exact all-false square matrices -/

def machineFalseSquareBuilderInput (n : ℕ) : List Bool :=
  pair (List.replicate n true)
    (boolVectorCode (List.replicate n false))

def machineFalseSquareBuilderState (n k : ℕ) : List Bool :=
  let word := machineFalseSquareBuilderInput n
  let row := List.replicate n false
  machineRepeatedRowMatrixPack (boolVectorCode row)
    (boolMatrixCode (List.replicate k row))
    (machineRepeatedRowMatrixBound word)

theorem machineFalseSquareBuilderInit_semantics (n : ℕ) :
    machineRepeatedRowMatrixInit (machineFalseSquareBuilderInput n) =
      machineFalseSquareBuilderState n 0 := by
  simp [machineRepeatedRowMatrixInit, machineFalseSquareBuilderInput,
    machineFalseSquareBuilderState, machineRepeatedRowMatrixRow,
    boolMatrixCode, binaryListCode]

theorem machineFalseSquareBuilderStep_semantics
    (n k : ℕ) (hk : k < n) :
    machineRepeatedRowMatrixStep (machineFalseSquareBuilderState n k) =
      machineFalseSquareBuilderState n (k + 1) := by
  let word := machineFalseSquareBuilderInput n
  let row := List.replicate n false
  have hrowLength : (boolVectorCode row).length = 4 * n := by
    simp [boolVectorCode, binaryListCode_length_eq_sum, row,
      boolElementCode, Nat.nsmul_eq_mul]
    omega
  have hmatrixLength :
      (boolMatrixCode (List.replicate (k + 1) row)).length =
        (k + 1) * (2 * (boolVectorCode row).length + 2) := by
    simp [boolMatrixCode, binaryListCode_length_eq_sum,
      Nat.nsmul_eq_mul]
  have hbound :
      (boolMatrixCode (List.replicate (k + 1) row)).length ≤
        (machineRepeatedRowMatrixBound word).length := by
    rw [hmatrixLength, hrowLength]
    simp only [machineRepeatedRowMatrixBound, machineBinaryMulWidth,
      word, machineFalseSquareBuilderInput, pair_length,
      List.length_replicate, List.length_append]
    have hrowCode :
        (boolVectorCode (List.replicate n false)).length = 4 * n := by
      simpa only [row] using hrowLength
    rw [hrowCode]
    nlinarith
  have htake :
      (boolMatrixCode (List.replicate (k + 1) row)).take
          (machineRepeatedRowMatrixBound word).length =
        boolMatrixCode (List.replicate (k + 1) row) :=
    List.take_of_length_le hbound
  simp only [machineRepeatedRowMatrixStep,
    machineFalseSquareBuilderState,
    machineRepeatedRowMatrixStateRow_pack,
    machineRepeatedRowMatrixStateAcc_pack,
    machineRepeatedRowMatrixStateBound_pack,
    machineRepeatedRowMatrixNextAcc,
    machineRepeatedRowMatrixCandidate]
  change machineRepeatedRowMatrixPack (boolVectorCode row)
      ((boolMatrixCode (List.replicate (k + 1) row)).take
        (machineRepeatedRowMatrixBound word).length)
      (machineRepeatedRowMatrixBound word) = _
  rw [htake]

theorem machineFalseSquareBuilderIterate_semantics (n : ℕ) : ∀ k ≤ n,
    (machineRepeatedRowMatrixStep)^[k]
        (machineRepeatedRowMatrixInit (machineFalseSquareBuilderInput n)) =
      machineFalseSquareBuilderState n k := by
  intro k hk
  induction k with
  | zero => exact machineFalseSquareBuilderInit_semantics n
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineFalseSquareBuilderStep_semantics n k (by omega)

@[simp] theorem machineRepeatedRowMatrixCode_falseSquare (n : ℕ) :
    machineRepeatedRowMatrixCode (machineFalseSquareBuilderInput n) =
      boolMatrixCode
        (List.replicate n (List.replicate n false)) := by
  rw [machineRepeatedRowMatrixCode, machineRepeatedRowMatrixFinalState]
  simp only [machineRepeatedRowMatrixRuler,
    machineFalseSquareBuilderInput, machinePairFirst_pair,
    List.length_replicate]
  change machineRepeatedRowMatrixStateAcc
      ((machineRepeatedRowMatrixStep)^[n]
        (machineRepeatedRowMatrixInit
          (machineFalseSquareBuilderInput n))) = _
  rw [machineFalseSquareBuilderIterate_semantics n n le_rfl]
  simp [machineFalseSquareBuilderState]

/-- Build all-false `n` by `n` Boolean storage from a canonical rational
matrix input of dimension `n`. -/
def machineFalseSquareMatrixCode (word : List Bool) : List Bool :=
  let ruler := machineMatrixDimensionUnary word
  let row := machineFalseVectorCode ruler
  machineRepeatedRowMatrixCode (pair ruler row)

theorem machineFalseSquareMatrixCode_mem_FP :
    machineFalseSquareMatrixCode ∈ Complexity.FP := by
  have hruler := machineMatrixDimensionUnary_mem_FP
  have hrow := machineCompose_mem_FP hruler machineFalseVectorCode_mem_FP
  have hpayload := machinePair_mem_FP hruler hrow
  simpa only [machineFalseSquareMatrixCode] using
    machineCompose_mem_FP hpayload machineRepeatedRowMatrixCode_mem_FP

@[simp] theorem machineFalseSquareMatrixCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineFalseSquareMatrixCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      boolMatrixCode
        (List.replicate n (List.replicate n false)) := by
  rw [machineFalseSquareMatrixCode, machineMatrixDimensionUnary_encode,
    machineFalseVectorCode_encode]
  exact machineRepeatedRowMatrixCode_falseSquare n

end BeyondBethe
