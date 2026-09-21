/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerEntryLength
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
import LeanPool.BeyondBethe.BeyondBethe.CertificateMagnitude

/-!
# Exact matrix entry-bit bound for the optimizer

This row-major transducer returns a unary ruler of length
`rationalMatrixEntryBitBound A`.  Its clamp and state envelope are explicit
on arbitrary bitstrings; the clamp is proved inactive on every canonical
matrix input.
-/

namespace BeyondBethe

open Complexity

def machineMatrixEntryLengthPack
    (rows current acc bound : List Bool) : List Bool :=
  pair rows (pair current (pair acc bound))

def machineMatrixEntryLengthRows (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMatrixEntryLengthCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMatrixEntryLengthAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineMatrixEntryLengthBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineMatrixEntryLengthEntry (state : List Bool) : List Bool :=
  machineListHead (machineMatrixEntryLengthCurrent state)

def machineMatrixEntryLengthCandidate (state : List Bool) : List Bool :=
  machineMatrixEntryLengthAcc state ++
    machineOptimizerEntryLengthRuler (machineMatrixEntryLengthEntry state)

def machineMatrixEntryLengthNextAcc (state : List Bool) : List Bool :=
  (machineMatrixEntryLengthCandidate state).take
    (machineMatrixEntryLengthBound state).length

def machineMatrixEntryLengthProcessEntry (state : List Bool) : List Bool :=
  machineMatrixEntryLengthPack
    (machineMatrixEntryLengthRows state)
    (machineListTail (machineMatrixEntryLengthCurrent state))
    (machineMatrixEntryLengthNextAcc state)
    (machineMatrixEntryLengthBound state)

def machineMatrixEntryLengthLoadRow (state : List Bool) : List Bool :=
  machineMatrixEntryLengthPack
    (machineListTail (machineMatrixEntryLengthRows state))
    (machineListHead (machineMatrixEntryLengthRows state))
    (machineMatrixEntryLengthAcc state)
    (machineMatrixEntryLengthBound state)

def machineMatrixEntryLengthAfterRow (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixEntryLengthRows state) state
    (machineMatrixEntryLengthLoadRow state)

def machineMatrixEntryLengthStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixEntryLengthCurrent state)
    (machineMatrixEntryLengthAfterRow state)
    (machineMatrixEntryLengthProcessEntry state)

def machineMatrixEntryLengthInputBound (word : List Bool) : List Bool :=
  let w2 := word ++ word
  let w4 := w2 ++ w2
  let w8 := w4 ++ w4
  let w16 := w8 ++ w8
  let w32 := w16 ++ w16
  let w64 := w32 ++ w32
  List.replicate 8 false ++ w64

def machineMatrixEntryLengthInit (word : List Bool) : List Bool :=
  machineMatrixEntryLengthPack (machineMatrixRowsWord word) [] [true]
    (machineMatrixEntryLengthInputBound word)

def machineMatrixEntryLengthWidth (word : List Bool) : List Bool :=
  let bound := machineMatrixEntryLengthInputBound word
  machineMatrixEntryLengthPack bound bound bound bound

def machineMatrixEntryLengthFinalState (word : List Bool) : List Bool :=
  (machineMatrixEntryLengthStep)^[word.length]
    (machineMatrixEntryLengthInit word)

/-- Exact unary matrix-entry bit bound on canonical inputs. -/
def machineMatrixEntryBitBoundRuler (word : List Bool) : List Bool :=
  machineMatrixEntryLengthAcc (machineMatrixEntryLengthFinalState word)

/-! ## Polynomial-time envelope -/

theorem machineMatrixEntryLengthRows_mem_FP :
    machineMatrixEntryLengthRows ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineMatrixEntryLengthCurrent_mem_FP :
    machineMatrixEntryLengthCurrent ∈ Complexity.FP := by
  simpa only [machineMatrixEntryLengthCurrent] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatrixEntryLengthAcc_mem_FP :
    machineMatrixEntryLengthAcc ∈ Complexity.FP := by
  simpa only [machineMatrixEntryLengthAcc] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineMatrixEntryLengthBound_mem_FP :
    machineMatrixEntryLengthBound ∈ Complexity.FP := by
  simpa only [machineMatrixEntryLengthBound] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
      machinePairSecond_mem_FP

theorem machineMatrixEntryLengthEntry_mem_FP :
    machineMatrixEntryLengthEntry ∈ Complexity.FP := by
  simpa only [machineMatrixEntryLengthEntry] using
    machineCompose_mem_FP machineMatrixEntryLengthCurrent_mem_FP
      machineListHead_mem_FP

theorem machineMatrixEntryLengthCandidate_mem_FP :
    machineMatrixEntryLengthCandidate ∈ Complexity.FP := by
  have hcost := machineCompose_mem_FP machineMatrixEntryLengthEntry_mem_FP
    machineOptimizerEntryLengthRuler_mem_FP
  exact machineAppend_mem_FP machineMatrixEntryLengthAcc_mem_FP hcost

theorem machineMatrixEntryLengthNextAcc_mem_FP :
    machineMatrixEntryLengthNextAcc ∈ Complexity.FP := by
  simpa only [machineMatrixEntryLengthNextAcc] using
    machineTake_mem_FP machineMatrixEntryLengthBound_mem_FP
      machineMatrixEntryLengthCandidate_mem_FP

theorem machineMatrixEntryLengthProcessEntry_mem_FP :
    machineMatrixEntryLengthProcessEntry ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixEntryLengthCurrent_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP machineMatrixEntryLengthRows_mem_FP
    (machinePair_mem_FP htail
      (machinePair_mem_FP machineMatrixEntryLengthNextAcc_mem_FP
        machineMatrixEntryLengthBound_mem_FP))

theorem machineMatrixEntryLengthLoadRow_mem_FP :
    machineMatrixEntryLengthLoadRow ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixEntryLengthRows_mem_FP
    machineListTail_mem_FP
  have hhead := machineCompose_mem_FP machineMatrixEntryLengthRows_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP hhead
      (machinePair_mem_FP machineMatrixEntryLengthAcc_mem_FP
        machineMatrixEntryLengthBound_mem_FP))

theorem machineMatrixEntryLengthAfterRow_mem_FP :
    machineMatrixEntryLengthAfterRow ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixEntryLengthRows_mem_FP id_mem_FP
    machineMatrixEntryLengthLoadRow_mem_FP

theorem machineMatrixEntryLengthStep_mem_FP :
    machineMatrixEntryLengthStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixEntryLengthCurrent_mem_FP
    machineMatrixEntryLengthAfterRow_mem_FP
    machineMatrixEntryLengthProcessEntry_mem_FP

theorem machineMatrixEntryLengthInputBound_mem_FP :
    machineMatrixEntryLengthInputBound ∈ Complexity.FP := by
  have h2 := machineAppend_mem_FP id_mem_FP id_mem_FP
  have h4 := machineAppend_mem_FP h2 h2
  have h8 := machineAppend_mem_FP h4 h4
  have h16 := machineAppend_mem_FP h8 h8
  have h32 := machineAppend_mem_FP h16 h16
  have h64 := machineAppend_mem_FP h32 h32
  simpa only [machineMatrixEntryLengthInputBound] using
    machineAppend_mem_FP
      (machineConst_mem_FP (List.replicate 8 false)) h64

theorem machineMatrixEntryLengthInit_mem_FP :
    machineMatrixEntryLengthInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixRowsWord_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP [true])
        machineMatrixEntryLengthInputBound_mem_FP))

theorem machineMatrixEntryLengthWidth_mem_FP :
    machineMatrixEntryLengthWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixEntryLengthInputBound_mem_FP
    (machinePair_mem_FP machineMatrixEntryLengthInputBound_mem_FP
      (machinePair_mem_FP machineMatrixEntryLengthInputBound_mem_FP
        machineMatrixEntryLengthInputBound_mem_FP))

@[simp] theorem machineMatrixEntryLengthRows_pack (rows current acc bound) :
    machineMatrixEntryLengthRows
        (machineMatrixEntryLengthPack rows current acc bound) = rows := by
  simp [machineMatrixEntryLengthRows, machineMatrixEntryLengthPack]

@[simp] theorem machineMatrixEntryLengthCurrent_pack (rows current acc bound) :
    machineMatrixEntryLengthCurrent
        (machineMatrixEntryLengthPack rows current acc bound) = current := by
  simp [machineMatrixEntryLengthCurrent, machineMatrixEntryLengthPack]

@[simp] theorem machineMatrixEntryLengthAcc_pack (rows current acc bound) :
    machineMatrixEntryLengthAcc
        (machineMatrixEntryLengthPack rows current acc bound) = acc := by
  simp [machineMatrixEntryLengthAcc, machineMatrixEntryLengthPack]

@[simp] theorem machineMatrixEntryLengthBound_pack (rows current acc bound) :
    machineMatrixEntryLengthBound
        (machineMatrixEntryLengthPack rows current acc bound) = bound := by
  simp [machineMatrixEntryLengthBound, machineMatrixEntryLengthPack]

@[simp] theorem machineMatrixEntryLengthInputBound_length (word : List Bool) :
    (machineMatrixEntryLengthInputBound word).length =
      8 + 64 * word.length := by
  simp [machineMatrixEntryLengthInputBound]
  omega

def MachineMatrixEntryLengthStateBound (word state : List Bool) : Prop :=
  state = machineMatrixEntryLengthPack
      (machineMatrixEntryLengthRows state)
      (machineMatrixEntryLengthCurrent state)
      (machineMatrixEntryLengthAcc state)
      (machineMatrixEntryLengthBound state) ∧
    (machineMatrixEntryLengthRows state).length ≤ word.length ∧
    (machineMatrixEntryLengthCurrent state).length ≤ word.length ∧
    (machineMatrixEntryLengthAcc state).length ≤
      (machineMatrixEntryLengthInputBound word).length ∧
    machineMatrixEntryLengthBound state =
      machineMatrixEntryLengthInputBound word

theorem machineMatrixEntryLengthInit_bound (word : List Bool) :
    MachineMatrixEntryLengthStateBound word
      (machineMatrixEntryLengthInit word) := by
  simp only [MachineMatrixEntryLengthStateBound,
    machineMatrixEntryLengthInit, machineMatrixEntryLengthRows_pack,
    machineMatrixEntryLengthCurrent_pack, machineMatrixEntryLengthAcc_pack,
    machineMatrixEntryLengthBound_pack]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineMatrixRowsWord] using machinePairSecond_length_le word
  · simp only [machineMatrixEntryLengthInputBound_length,
      List.length_singleton]
    omega

theorem machineMatrixEntryLengthStep_bound {word state : List Bool}
    (hstate : MachineMatrixEntryLengthStateBound word state) :
    MachineMatrixEntryLengthStateBound word
      (machineMatrixEntryLengthStep state) := by
  rcases hstate with ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  by_cases hc : machineMatrixEntryLengthCurrent state = []
  · rw [machineMatrixEntryLengthStep, hc, machineIfEmpty_nil]
    by_cases hr : machineMatrixEntryLengthRows state = []
    · rw [machineMatrixEntryLengthAfterRow, hr, machineIfEmpty_nil]
      exact ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
    · rw [machineMatrixEntryLengthAfterRow]
      cases hrowsCode : machineMatrixEntryLengthRows state with
      | nil => exact False.elim (hr hrowsCode)
      | cons bit tail =>
          rw [machineIfEmpty_cons, machineMatrixEntryLengthLoadRow]
          simp only [MachineMatrixEntryLengthStateBound,
            machineMatrixEntryLengthRows_pack,
            machineMatrixEntryLengthCurrent_pack,
            machineMatrixEntryLengthAcc_pack,
            machineMatrixEntryLengthBound_pack]
          refine ⟨trivial, ?_, ?_, hacc, hbound⟩
          · exact (machinePairSecond_length_le
              (machineMatrixEntryLengthRows state)).trans hrows
          · exact (machinePairFirst_length_le
              (machineMatrixEntryLengthRows state)).trans hrows
  · rw [machineMatrixEntryLengthStep]
    cases hcurrentCode : machineMatrixEntryLengthCurrent state with
    | nil => exact False.elim (hc hcurrentCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixEntryLengthProcessEntry]
        simp only [MachineMatrixEntryLengthStateBound,
          machineMatrixEntryLengthRows_pack,
          machineMatrixEntryLengthCurrent_pack,
          machineMatrixEntryLengthAcc_pack,
          machineMatrixEntryLengthBound_pack]
        refine ⟨trivial, hrows, ?_, ?_, hbound⟩
        · exact (machinePairSecond_length_le
            (machineMatrixEntryLengthCurrent state)).trans hcurrent
        · rw [machineMatrixEntryLengthNextAcc, hbound]
          exact List.length_take_le _ _

theorem machineMatrixEntryLengthIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixEntryLengthStateBound word
      ((machineMatrixEntryLengthStep)^[k]
        (machineMatrixEntryLengthInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixEntryLengthInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixEntryLengthStep_bound ih

theorem machineMatrixEntryLengthIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineMatrixEntryLengthStep)^[iterations]
      (machineMatrixEntryLengthInit word)).length ≤
        (machineMatrixEntryLengthWidth word).length := by
  rcases machineMatrixEntryLengthIterate_bound word iterations with
    ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineMatrixEntryLengthPack,
    machineMatrixEntryLengthWidth, pair_length]
  have hword : word.length ≤
      (machineMatrixEntryLengthInputBound word).length := by
    simp only [machineMatrixEntryLengthInputBound_length]
    omega
  omega

theorem machineMatrixEntryLengthFinalState_mem_FP :
    machineMatrixEntryLengthFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixEntryLengthStep_mem_FP
    machineMatrixEntryLengthInit_mem_FP id_mem_FP
    machineMatrixEntryLengthWidth_mem_FP
    machineMatrixEntryLengthIterate_length_le_width

theorem machineMatrixEntryBitBoundRuler_mem_FP :
    machineMatrixEntryBitBoundRuler ∈ Complexity.FP := by
  simpa only [machineMatrixEntryBitBoundRuler] using
    machineCompose_mem_FP machineMatrixEntryLengthFinalState_mem_FP
      machineMatrixEntryLengthAcc_mem_FP

/-! ## Exact semantics -/

def matrixEntryLengthListCost (xs : List ℚ) : ℕ :=
  (xs.map fun q ↦ encodedBitLength ℚ q).sum

def matrixEntryLengthRowsCost (rows : List (List ℚ)) : ℕ :=
  (rows.map matrixEntryLengthListCost).sum

structure MatrixEntryLengthSemState where
  rows : List (List ℚ)
  current : List ℚ
  acc : ℕ

def matrixEntryLengthSemCode (bound : List Bool)
    (s : MatrixEntryLengthSemState) : List Bool :=
  machineMatrixEntryLengthPack
    (binaryListCode (binaryListCode rationalEntryBinaryCode) s.rows)
    (binaryListCode rationalEntryBinaryCode s.current)
    (List.replicate s.acc true) bound

def matrixEntryLengthSemStep :
    MatrixEntryLengthSemState → MatrixEntryLengthSemState
  | ⟨[], [], acc⟩ => ⟨[], [], acc⟩
  | ⟨row :: rows, [], acc⟩ => ⟨rows, row, acc⟩
  | ⟨rows, q :: qs, acc⟩ =>
      ⟨rows, qs, acc + encodedBitLength ℚ q⟩

def MatrixEntryLengthSemInvariant
    (boundLength : ℕ) (s : MatrixEntryLengthSemState) : Prop :=
  s.acc + matrixEntryLengthListCost s.current +
    matrixEntryLengthRowsCost s.rows ≤ boundLength

theorem matrixEntryLengthSemStep_invariant {L : ℕ}
    {s : MatrixEntryLengthSemState}
    (hs : MatrixEntryLengthSemInvariant L s) :
    MatrixEntryLengthSemInvariant L (matrixEntryLengthSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | cons q qs =>
      simpa [MatrixEntryLengthSemInvariant, matrixEntryLengthSemStep,
        matrixEntryLengthListCost, Nat.add_assoc] using hs
  | nil =>
      cases rows with
      | nil => simpa [MatrixEntryLengthSemInvariant,
          matrixEntryLengthSemStep] using hs
      | cons row rows =>
          simpa [MatrixEntryLengthSemInvariant, matrixEntryLengthSemStep,
            matrixEntryLengthListCost, matrixEntryLengthRowsCost,
            Nat.add_assoc] using hs

theorem machineMatrixEntryLengthStep_semantics
    (bound : List Bool) (s : MatrixEntryLengthSemState)
    (hs : MatrixEntryLengthSemInvariant bound.length s) :
    machineMatrixEntryLengthStep (matrixEntryLengthSemCode bound s) =
      matrixEntryLengthSemCode bound (matrixEntryLengthSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil =>
          simp [machineMatrixEntryLengthStep,
            machineMatrixEntryLengthAfterRow, matrixEntryLengthSemCode,
            matrixEntryLengthSemStep, binaryListCode]
      | cons row rows =>
          rw [matrixEntryLengthSemCode, matrixEntryLengthSemStep,
            machineMatrixEntryLengthStep]
          simp only [machineMatrixEntryLengthCurrent_pack, binaryListCode,
            machineIfEmpty_nil, machineMatrixEntryLengthAfterRow,
            machineMatrixEntryLengthRows_pack]
          have hpair : pair (binaryListCode rationalEntryBinaryCode row)
              (binaryListCode (binaryListCode rationalEntryBinaryCode) rows) ≠
              [] := by
            intro h
            have hlen := congrArg List.length h
            simp at hlen
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hpair]
          simp [machineMatrixEntryLengthLoadRow,
            matrixEntryLengthSemCode, machineListHead, machineListTail]
  | cons q qs =>
      have hfit : acc + encodedBitLength ℚ q ≤ bound.length := by
        simp [MatrixEntryLengthSemInvariant,
          matrixEntryLengthListCost] at hs
        omega
      rw [matrixEntryLengthSemCode, matrixEntryLengthSemStep,
        machineMatrixEntryLengthStep]
      simp only [machineMatrixEntryLengthCurrent_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineMatrixEntryLengthProcessEntry,
        machineMatrixEntryLengthRows_pack,
        machineMatrixEntryLengthCurrent_pack,
        machineMatrixEntryLengthAcc_pack,
        machineMatrixEntryLengthBound_pack,
        machineListTail_cons, machineMatrixEntryLengthNextAcc,
        machineMatrixEntryLengthCandidate,
        machineMatrixEntryLengthEntry, machineListHead_cons,
        machineOptimizerEntryLengthRuler_encode]
      rw [show List.replicate acc true ++
          List.replicate (encodedBitLength ℚ q) true =
        List.replicate (acc + encodedBitLength ℚ q) true by
            exact (List.replicate_add _ _ _).symm,
        (List.take_eq_self_iff _).mpr (by simpa using hfit)]
      rfl

theorem machineMatrixEntryLengthIterate_semantics
    (bound : List Bool) (s : MatrixEntryLengthSemState)
    (hs : MatrixEntryLengthSemInvariant bound.length s) : ∀ k,
    (machineMatrixEntryLengthStep)^[k]
        (matrixEntryLengthSemCode bound s) =
      matrixEntryLengthSemCode bound ((matrixEntryLengthSemStep)^[k] s) := by
  intro k
  have hinv : ∀ t,
      MatrixEntryLengthSemInvariant bound.length
        ((matrixEntryLengthSemStep)^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact matrixEntryLengthSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineMatrixEntryLengthStep_semantics bound _ (hinv k)

theorem matrixEntryLengthSem_processRow
    (rows : List (List ℚ)) (row : List ℚ) (acc : ℕ) :
    (matrixEntryLengthSemStep)^[row.length]
        ⟨rows, row, acc⟩ =
      ⟨rows, [], acc + matrixEntryLengthListCost row⟩ := by
  induction row generalizing acc with
  | nil => simp [matrixEntryLengthListCost]
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        matrixEntryLengthSemStep, ih]
      simp [matrixEntryLengthListCost, Nat.add_assoc]

theorem matrixEntryLengthSem_processRows
    (rows : List (List ℚ)) (acc : ℕ) :
    (matrixEntryLengthSemStep)^[matrixNonnegativeRowsWork rows]
        ⟨rows, [], acc⟩ =
      ⟨[], [], acc + matrixEntryLengthRowsCost rows⟩ := by
  induction rows generalizing acc with
  | nil => simp [matrixNonnegativeRowsWork, matrixEntryLengthRowsCost]
  | cons row rows ih =>
      rw [matrixNonnegativeRowsWork, show 1 + row.length +
          matrixNonnegativeRowsWork rows =
          matrixNonnegativeRowsWork rows + row.length + 1 by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, matrixEntryLengthSemStep,
        matrixEntryLengthSem_processRow, ih]
      simp [matrixEntryLengthRowsCost, Nat.add_assoc]

theorem machineMatrixEntryLength_done_iterate
    (extra : ℕ) (acc : ℕ) (bound : List Bool) :
    (machineMatrixEntryLengthStep)^[extra]
        (machineMatrixEntryLengthPack [] []
          (List.replicate acc true) bound) =
      machineMatrixEntryLengthPack [] []
        (List.replicate acc true) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineMatrixEntryLengthStep, machineMatrixEntryLengthAfterRow]

theorem matrixEntryLengthRowsCost_eq_matrixBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    1 + matrixEntryLengthRowsCost (rationalMatrixRows A) =
      rationalMatrixEntryBitBound A := by
  simp only [matrixEntryLengthRowsCost, matrixEntryLengthListCost,
    rationalMatrixRows, rationalMatrixEntryBitBound,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem machineMatrixEntryLengthFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixEntryLengthFinalState
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      machineMatrixEntryLengthPack [] []
        (List.replicate (rationalMatrixEntryBitBound A) true)
        (machineMatrixEntryLengthInputBound
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) := by
  let rows := rationalMatrixRows A
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let bound := machineMatrixEntryLengthInputBound word
  let s : MatrixEntryLengthSemState := ⟨rows, [], 1⟩
  have hrowsLength :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machineMatrixRowsWord word).length := by
        simpa only [word, rows] using congrArg List.length
          (machineMatrixRowsWord_encode A).symm
      _ ≤ word.length := by
        simpa only [machineMatrixRowsWord] using
          machinePairSecond_length_le word
  have hcost : rationalMatrixEntryBitBound A ≤ bound.length := by
    by_cases hn : n = 0
    · subst n
      simp only [rationalMatrixEntryBitBound, rationalMatrixRows,
        Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero, bound,
        machineMatrixEntryLengthInputBound_length]
      omega
    · have hmachine := rationalMatrixEntryBitBound_le_machineCode
          (Nat.pos_of_ne_zero hn) A
      have hmachine' : rationalMatrixEntryBitBound A ≤ 32 * word.length := by
        simpa only [word] using hmachine
      simp only [bound, machineMatrixEntryLengthInputBound_length]
      omega
  have hinv : MatrixEntryLengthSemInvariant bound.length s := by
    simpa only [MatrixEntryLengthSemInvariant, s,
      matrixEntryLengthListCost, List.map_nil, List.sum_nil, Nat.add_zero,
      rows, matrixEntryLengthRowsCost_eq_matrixBound] using hcost
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsLength
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  have hinit : machineMatrixEntryLengthInit word =
      matrixEntryLengthSemCode bound s := by
    simp [machineMatrixEntryLengthInit, matrixEntryLengthSemCode,
      s, rows, word, bound, binaryListCode]
  change machineMatrixEntryLengthFinalState word = _
  rw [machineMatrixEntryLengthFinalState, hsplit,
    Function.iterate_add_apply, hinit,
    machineMatrixEntryLengthIterate_semantics bound s hinv,
    matrixEntryLengthSem_processRows]
  simp only [matrixEntryLengthSemCode, binaryListCode]
  rw [machineMatrixEntryLength_done_iterate]
  congr 2
  rw [matrixEntryLengthRowsCost_eq_matrixBound]

@[simp] theorem machineMatrixEntryBitBoundRuler_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixEntryBitBoundRuler
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate (rationalMatrixEntryBitBound A) true := by
  rw [machineMatrixEntryBitBoundRuler,
    machineMatrixEntryLengthFinalState_encode]
  simp

end BeyondBethe
