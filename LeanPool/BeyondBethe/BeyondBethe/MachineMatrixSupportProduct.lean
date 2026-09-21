/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
import LeanPool.BeyondBethe.BeyondBethe.MachineBooleanMemory
import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly

/-!
# Row-major support product of a rational matrix

The support floor multiplies every nonzero matrix entry while letting a zero
entry contribute the neutral factor one.  This file implements that scan on
the concrete nested binary matrix encoding.  The accumulator is an unreduced
rational; a quadratic clamp is total on malformed inputs and is proved
inactive on canonical matrices.
-/

namespace BeyondBethe

open Complexity

def machineMatrixSupportNonzeroFlag (state : List Bool) : List Bool :=
  machineRawRatNeBit
    (pair (machineMatrixRawSumEntry state)
      (rawRatBinaryCode RawRat.zero))

def machineMatrixSupportFactorCode (state : List Bool) : List Bool :=
  machineIfHead (machineMatrixSupportNonzeroFlag state)
    (machineMatrixRawSumEntry state) (rawRatBinaryCode RawRat.one)

def machineMatrixSupportCandidate (state : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineMatrixRawSumAcc state)
      (machineMatrixSupportFactorCode state))

def machineMatrixSupportNextAcc (state : List Bool) : List Bool :=
  (machineMatrixSupportCandidate state).take
    (machineMatrixRawSumBound state).length

def machineMatrixSupportProcessEntry (state : List Bool) : List Bool :=
  machineMatrixRawSumPack
    (machineMatrixRawSumRows state)
    (machineListTail (machineMatrixRawSumCurrent state))
    (machineMatrixSupportNextAcc state)
    (machineMatrixRawSumBound state)

def machineMatrixSupportLoadRow (state : List Bool) : List Bool :=
  machineMatrixRawSumLoadRow state

def machineMatrixSupportAfterRow (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixRawSumRows state) state
    (machineMatrixSupportLoadRow state)

def machineMatrixSupportStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixRawSumCurrent state)
    (machineMatrixSupportAfterRow state)
    (machineMatrixSupportProcessEntry state)

def machineMatrixSupportInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineMatrixSupportInit (word : List Bool) : List Bool :=
  machineMatrixRawSumPack (machineMatrixRowsWord word) []
    (rawRatBinaryCode RawRat.one) (machineMatrixSupportInputBound word)

def machineMatrixSupportWidth (word : List Bool) : List Bool :=
  let bound := machineMatrixSupportInputBound word
  machineMatrixRawSumPack word word bound bound

def machineMatrixSupportFinalState (word : List Bool) : List Bool :=
  (machineMatrixSupportStep)^[word.length] (machineMatrixSupportInit word)

def machineMatrixSupportRawCode (word : List Bool) : List Bool :=
  machineMatrixRawSumAcc (machineMatrixSupportFinalState word)

def machineMatrixSupportProductCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineMatrixSupportRawCode word)

theorem machineMatrixSupportNonzeroFlag_mem_FP :
    machineMatrixSupportNonzeroFlag ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixRawSumEntry_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
  simpa only [machineMatrixSupportNonzeroFlag] using
    machineCompose_mem_FP hpair machineRawRatNeBit_mem_FP

theorem machineMatrixSupportFactorCode_mem_FP :
    machineMatrixSupportFactorCode ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineMatrixSupportNonzeroFlag_mem_FP
    machineMatrixRawSumEntry_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))

theorem machineMatrixSupportCandidate_mem_FP :
    machineMatrixSupportCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixRawSumAcc_mem_FP
    machineMatrixSupportFactorCode_mem_FP
  simpa only [machineMatrixSupportCandidate] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineMatrixSupportNextAcc_mem_FP :
    machineMatrixSupportNextAcc ∈ Complexity.FP := by
  simpa only [machineMatrixSupportNextAcc] using
    machineTake_mem_FP machineMatrixRawSumBound_mem_FP
      machineMatrixSupportCandidate_mem_FP

theorem machineMatrixSupportProcessEntry_mem_FP :
    machineMatrixSupportProcessEntry ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixRawSumCurrent_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP machineMatrixRawSumRows_mem_FP
    (machinePair_mem_FP htail
      (machinePair_mem_FP machineMatrixSupportNextAcc_mem_FP
        machineMatrixRawSumBound_mem_FP))

theorem machineMatrixSupportLoadRow_mem_FP :
    machineMatrixSupportLoadRow ∈ Complexity.FP := by
  simpa only [machineMatrixSupportLoadRow] using
    machineMatrixRawSumLoadRow_mem_FP

theorem machineMatrixSupportAfterRow_mem_FP :
    machineMatrixSupportAfterRow ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixRawSumRows_mem_FP id_mem_FP
    machineMatrixSupportLoadRow_mem_FP

theorem machineMatrixSupportStep_mem_FP :
    machineMatrixSupportStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixRawSumCurrent_mem_FP
    machineMatrixSupportAfterRow_mem_FP
    machineMatrixSupportProcessEntry_mem_FP

theorem machineMatrixSupportInputBound_mem_FP :
    machineMatrixSupportInputBound ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineMatrixSupportInit_mem_FP :
    machineMatrixSupportInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixRowsWord_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
        machineMatrixSupportInputBound_mem_FP))

theorem machineMatrixSupportWidth_mem_FP :
    machineMatrixSupportWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineMatrixSupportInputBound_mem_FP
        machineMatrixSupportInputBound_mem_FP))

theorem machineMatrixSupportInit_bound (word : List Bool) :
    MachineMatrixRawSumStateBound word (machineMatrixSupportInit word) := by
  simp only [MachineMatrixRawSumStateBound, machineMatrixSupportInit,
    machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
    machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
  refine ⟨trivial, ?_, by simp, ?_, rfl⟩
  · simpa only [machineMatrixRowsWord] using machinePairSecond_length_le word
  · simp [machineMatrixRawSumInputBound, machineBinaryMulWidth,
      rawRatBinaryCode, RawRat.one, integerBinaryCode]
    nlinarith [sq_nonneg (word.length + 16)]

theorem machineMatrixSupportStep_bound {word state : List Bool}
    (hstate : MachineMatrixRawSumStateBound word state) :
    MachineMatrixRawSumStateBound word (machineMatrixSupportStep state) := by
  rcases hstate with ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  by_cases hc : machineMatrixRawSumCurrent state = []
  · rw [machineMatrixSupportStep, hc, machineIfEmpty_nil]
    by_cases hr : machineMatrixRawSumRows state = []
    · rw [machineMatrixSupportAfterRow, hr, machineIfEmpty_nil]
      exact ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
    · rw [machineMatrixSupportAfterRow]
      cases hrowsCode : machineMatrixRawSumRows state with
      | nil => exact False.elim (hr hrowsCode)
      | cons bit tail =>
          rw [machineIfEmpty_cons, machineMatrixSupportLoadRow]
          rw [machineMatrixRawSumLoadRow]
          simp only [MachineMatrixRawSumStateBound,
            machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
            machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
          refine ⟨trivial, ?_, ?_, hacc, hbound⟩
          · exact (machinePairSecond_length_le
              (machineMatrixRawSumRows state)).trans hrows
          · exact (machinePairFirst_length_le
              (machineMatrixRawSumRows state)).trans hrows
  · rw [machineMatrixSupportStep]
    cases hcurrentCode : machineMatrixRawSumCurrent state with
    | nil => exact False.elim (hc hcurrentCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixSupportProcessEntry]
        simp only [MachineMatrixRawSumStateBound,
          machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
          machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
        refine ⟨trivial, hrows, ?_, ?_, hbound⟩
        · exact (machinePairSecond_length_le
            (machineMatrixRawSumCurrent state)).trans hcurrent
        · rw [machineMatrixSupportNextAcc, hbound]
          exact List.length_take_le _ _

theorem machineMatrixSupportIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixRawSumStateBound word
      ((machineMatrixSupportStep)^[k] (machineMatrixSupportInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixSupportInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixSupportStep_bound ih

theorem machineMatrixSupportIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineMatrixSupportStep)^[iterations]
      (machineMatrixSupportInit word)).length ≤
        (machineMatrixSupportWidth word).length := by
  rcases machineMatrixSupportIterate_bound word iterations with
    ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  have hbound' :
      machineMatrixRawSumBound
          ((machineMatrixSupportStep)^[iterations]
            (machineMatrixSupportInit word)) =
        machineMatrixSupportInputBound word := by
    simpa only [machineMatrixSupportInputBound,
      machineMatrixRawSumInputBound] using hbound
  have hacc' :
      (machineMatrixRawSumAcc
          ((machineMatrixSupportStep)^[iterations]
            (machineMatrixSupportInit word))).length ≤
        (machineMatrixSupportInputBound word).length := by
    simpa only [machineMatrixSupportInputBound,
      machineMatrixRawSumInputBound] using hacc
  rw [hdecomp, hbound']
  simp only [machineMatrixRawSumPack, machineMatrixSupportWidth, pair_length]
  omega

theorem machineMatrixSupportFinalState_mem_FP :
    machineMatrixSupportFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixSupportStep_mem_FP
    machineMatrixSupportInit_mem_FP id_mem_FP
    machineMatrixSupportWidth_mem_FP
    machineMatrixSupportIterate_length_le_width

theorem machineMatrixSupportRawCode_mem_FP :
    machineMatrixSupportRawCode ∈ Complexity.FP := by
  simpa only [machineMatrixSupportRawCode] using
    machineCompose_mem_FP machineMatrixSupportFinalState_mem_FP
      machineMatrixRawSumAcc_mem_FP

theorem machineMatrixSupportProductCode_mem_FP :
    machineMatrixSupportProductCode ∈ Complexity.FP := by
  simpa only [machineMatrixSupportProductCode] using
    machineCompose_mem_FP machineMatrixSupportRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

/-! ## Exact semantics -/

def rawRatSupportFactor (q : ℚ) : RawRat :=
  if q = 0 then RawRat.one else rawRatOfRat q

def rawRatListSupportProduct : RawRat → List ℚ → RawRat
  | acc, [] => acc
  | acc, q :: qs =>
      rawRatListSupportProduct (acc.mul (rawRatSupportFactor q)) qs

def rawRatRowsSupportProduct : RawRat → List (List ℚ) → RawRat
  | acc, [] => acc
  | acc, row :: rows =>
      rawRatRowsSupportProduct (rawRatListSupportProduct acc row) rows

def matrixSupportSemStep (s : MatrixRawSumSemState) : MatrixRawSumSemState :=
  match s.current with
  | q :: qs => ⟨s.rows, qs, s.acc.mul (rawRatSupportFactor q)⟩
  | [] =>
      match s.rows with
      | row :: rows => ⟨rows, row, s.acc⟩
      | [] => s

def MatrixSupportSemInvariant (budget : ℕ)
    (s : MatrixRawSumSemState) : Prop :=
  rawRatWidth s.acc + rawRatListCost s.current + rawRatRowsCost s.rows ≤ budget

theorem rawRatWidth_supportFactor_le (q : ℚ) :
    rawRatWidth (rawRatSupportFactor q) ≤
      rawRatWidth (rawRatOfRat q) + 1 := by
  by_cases hq : q = 0
  · simp [rawRatSupportFactor, hq, rawRatWidth_one]
  · simp [rawRatSupportFactor, hq]

theorem matrixSupportSemStep_invariant {budget : ℕ}
    {s : MatrixRawSumSemState} (hs : MatrixSupportSemInvariant budget s) :
    MatrixSupportSemInvariant budget (matrixSupportSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil => exact hs
      | cons row rows =>
          simp [MatrixSupportSemInvariant, matrixSupportSemStep,
            rawRatRowsCost, rawRatListCost] at hs ⊢
          omega
  | cons q qs =>
      have hmul := rawRatWidth_mul_le acc (rawRatSupportFactor q)
      have hfactor := rawRatWidth_supportFactor_le q
      simp only [MatrixSupportSemInvariant, matrixSupportSemStep,
        rawRatListCost, List.map_cons, List.sum_cons] at hs ⊢
      omega

theorem matrixSupportBound_large (word : List Bool) :
    4 + 3 * (1 + word.length) ≤
      (machineMatrixSupportInputBound word).length := by
  simp only [machineMatrixSupportInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

@[simp] theorem machineMatrixSupportFactorCode_semantics
    (rows : List (List ℚ)) (q : ℚ) (qs : List ℚ)
    (acc : RawRat) (bound : List Bool) :
    machineMatrixSupportFactorCode
        (matrixRawSumSemCode bound ⟨rows, q :: qs, acc⟩) =
      rawRatBinaryCode (rawRatSupportFactor q) := by
  rw [machineMatrixSupportFactorCode, machineMatrixSupportNonzeroFlag]
  simp only [matrixRawSumSemCode, machineMatrixRawSumEntry,
    machineMatrixRawSumCurrent_pack, machineListHead_cons,
    ← rawRatBinaryCode_rawRatOfRat, machineRawRatNeBit_encode,
    RawRat.value_zero, rawRatOfRat_value]
  by_cases hq : q = 0
  · simp [hq, rawRatSupportFactor]
  · simp [hq, rawRatSupportFactor]

theorem machineMatrixSupportStep_semantics
    (word : List Bool) (s : MatrixRawSumSemState)
    (hs : MatrixSupportSemInvariant (1 + word.length) s) :
    machineMatrixSupportStep
        (matrixRawSumSemCode (machineMatrixSupportInputBound word) s) =
      matrixRawSumSemCode (machineMatrixSupportInputBound word)
        (matrixSupportSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil =>
          simp [matrixRawSumSemCode, matrixSupportSemStep,
            machineMatrixSupportStep, machineMatrixSupportAfterRow,
            binaryListCode]
      | cons row rows =>
          rw [matrixRawSumSemCode, matrixSupportSemStep,
            machineMatrixSupportStep]
          simp only [machineMatrixRawSumCurrent_pack, binaryListCode,
            machineIfEmpty_nil, machineMatrixSupportAfterRow,
            machineMatrixRawSumRows_pack]
          have hpair : pair (binaryListCode rationalEntryBinaryCode row)
              (binaryListCode (binaryListCode rationalEntryBinaryCode) rows) ≠ [] := by
            intro h
            have hlen := congrArg List.length h
            simp at hlen
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hpair]
          simp [machineMatrixSupportLoadRow, machineMatrixRawSumLoadRow,
            matrixRawSumSemCode, machineListHead, machineListTail]
  | cons q qs =>
      have hnext :
          rawRatWidth (acc.mul (rawRatSupportFactor q)) ≤
            1 + word.length := by
        have hinv := matrixSupportSemStep_invariant hs
        have hinv' : rawRatWidth (acc.mul (rawRatSupportFactor q)) +
            rawRatListCost qs + rawRatRowsCost rows ≤ 1 + word.length := by
          simpa only [MatrixSupportSemInvariant,
            matrixSupportSemStep] using hinv
        omega
      have hcode :
          (rawRatBinaryCode (acc.mul (rawRatSupportFactor q))).length ≤
            (machineMatrixSupportInputBound word).length :=
        (rawRatBinaryCode_length_le_width _).trans
          ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans
            (matrixSupportBound_large word))
      have hfactor :
          machineMatrixSupportFactorCode
              (machineMatrixRawSumPack
                (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
                (binaryListCode rationalEntryBinaryCode (q :: qs))
                (rawRatBinaryCode acc)
                (machineMatrixSupportInputBound word)) =
            rawRatBinaryCode (rawRatSupportFactor q) := by
        simpa only [matrixRawSumSemCode] using
          machineMatrixSupportFactorCode_semantics rows q qs acc
            (machineMatrixSupportInputBound word)
      rw [matrixRawSumSemCode, matrixSupportSemStep,
        machineMatrixSupportStep]
      simp only [machineMatrixRawSumCurrent_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineMatrixSupportProcessEntry,
        machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
        machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack,
        machineListTail_cons, machineMatrixSupportNextAcc,
        machineMatrixSupportCandidate]
      rw [hfactor, machineRawRatMulCode_encode]
      rw [(List.take_eq_self_iff _).mpr hcode]
      rfl

theorem machineMatrixSupportIterate_semantics
    (word : List Bool) (s : MatrixRawSumSemState)
    (hs : MatrixSupportSemInvariant (1 + word.length) s) : ∀ k,
    (machineMatrixSupportStep)^[k]
        (matrixRawSumSemCode (machineMatrixSupportInputBound word) s) =
      matrixRawSumSemCode (machineMatrixSupportInputBound word)
        ((matrixSupportSemStep)^[k] s) := by
  intro k
  have hinv : ∀ t : ℕ,
      MatrixSupportSemInvariant (1 + word.length)
        ((matrixSupportSemStep)^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact matrixSupportSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineMatrixSupportStep_semantics word _ (hinv k)

theorem matrixSupportSem_processRow
    (rows : List (List ℚ)) (row : List ℚ) (acc : RawRat) :
    (matrixSupportSemStep)^[row.length] ⟨rows, row, acc⟩ =
      ⟨rows, [], rawRatListSupportProduct acc row⟩ := by
  induction row generalizing acc with
  | nil => rfl
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        matrixSupportSemStep, ih]
      rfl

theorem matrixSupportSem_processRows
    (rows : List (List ℚ)) (acc : RawRat) :
    (matrixSupportSemStep)^[matrixNonnegativeRowsWork rows]
        ⟨rows, [], acc⟩ =
      ⟨[], [], rawRatRowsSupportProduct acc rows⟩ := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rows ih =>
      rw [matrixNonnegativeRowsWork, show 1 + row.length +
          matrixNonnegativeRowsWork rows =
          matrixNonnegativeRowsWork rows + row.length + 1 by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, matrixSupportSemStep,
        matrixSupportSem_processRow, ih, rawRatRowsSupportProduct]

theorem machineMatrixSupport_done_iterate
    (extra : ℕ) (acc : RawRat) (bound : List Bool) :
    (machineMatrixSupportStep)^[extra]
        (machineMatrixRawSumPack [] [] (rawRatBinaryCode acc) bound) =
      machineMatrixRawSumPack [] [] (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineMatrixSupportStep, machineMatrixSupportAfterRow]

theorem machineMatrixSupportFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixSupportFinalState
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      machineMatrixRawSumPack [] []
        (rawRatBinaryCode
          (rawRatRowsSupportProduct RawRat.one (rationalMatrixRows A)))
        (machineMatrixSupportInputBound
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) := by
  let rows := rationalMatrixRows A
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let s : MatrixRawSumSemState := ⟨rows, [], RawRat.one⟩
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
  have hinv : MatrixSupportSemInvariant (1 + word.length) s := by
    simp only [MatrixSupportSemInvariant, s, rawRatListCost,
      List.map_nil, List.sum_nil, rawRatWidth_one, Nat.add_zero]
    exact Nat.add_le_add_left
      ((rawRatRowsCost_le_codeLength rows).trans hrowsLength) 1
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsLength
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  have hinit : machineMatrixSupportInit word =
      matrixRawSumSemCode (machineMatrixSupportInputBound word) s := by
    simp [machineMatrixSupportInit, matrixRawSumSemCode, s, word, rows,
      binaryListCode]
  change machineMatrixSupportFinalState word = _
  rw [machineMatrixSupportFinalState, hsplit, Function.iterate_add_apply,
    hinit, machineMatrixSupportIterate_semantics word s hinv,
    matrixSupportSem_processRows]
  simp only [matrixRawSumSemCode, binaryListCode]
  rw [machineMatrixSupport_done_iterate]

@[simp] theorem machineMatrixSupportRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixSupportRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawRatRowsSupportProduct RawRat.one (rationalMatrixRows A)) := by
  rw [machineMatrixSupportRawCode, machineMatrixSupportFinalState_encode]
  simp

@[simp] theorem machineMatrixSupportProductCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixSupportProductCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode
        (binaryNormalizeRawRat
          (rawRatRowsSupportProduct RawRat.one (rationalMatrixRows A))) := by
  rw [machineMatrixSupportProductCode,
    machineMatrixSupportRawCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

theorem rawRatSupportFactor_value (q : ℚ) :
    (rawRatSupportFactor q).value = if q = 0 then 1 else q := by
  by_cases hq : q = 0
  · simp [rawRatSupportFactor, hq, RawRat.value_one]
  · simp [rawRatSupportFactor, hq, rawRatOfRat_value]

theorem rawRatListSupportProduct_value (acc : RawRat) : ∀ xs : List ℚ,
    (rawRatListSupportProduct acc xs).value =
      acc.value * (xs.map fun q ↦ if q = 0 then 1 else q).prod := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListSupportProduct]
  | cons q qs ih =>
      rw [rawRatListSupportProduct, ih, RawRat.value_mul,
        rawRatSupportFactor_value]
      simp only [List.map_cons, List.prod_cons]
      ring

theorem rawRatRowsSupportProduct_value (acc : RawRat) :
    ∀ rows : List (List ℚ),
    (rawRatRowsSupportProduct acc rows).value =
      acc.value *
        (rows.map fun row ↦
          (row.map fun q ↦ if q = 0 then 1 else q).prod).prod := by
  intro rows
  induction rows generalizing acc with
  | nil => simp [rawRatRowsSupportProduct]
  | cons row rows ih =>
      rw [rawRatRowsSupportProduct, ih,
        rawRatListSupportProduct_value]
      simp only [List.map_cons, List.prod_cons]
      ring

theorem rawRatRowsSupportProduct_eq_rationalSupportFloor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (rawRatRowsSupportProduct RawRat.one
      (rationalMatrixRows A)).value = rationalSupportFloor A := by
  rw [rawRatRowsSupportProduct_value]
  simp only [RawRat.value_one, one_mul, rationalMatrixRows, List.map_ofFn,
    List.prod_ofFn, Function.comp_apply]
  have hproduct :
      (∏ i : Fin n, ∏ j : Fin n,
          if A i j = 0 then 1 else A i j) =
        ∏ p ∈ (Finset.univ.product Finset.univ),
          if A p.1 p.2 = 0 then 1 else A p.1 p.2 := by
    simpa using
      (Finset.prod_product' (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun i j ↦ if A i j = 0 then 1 else A i j)).symm
  rw [hproduct, rationalSupportFloor]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [rationalSupportFactor]

@[simp] theorem machineMatrixSupportProductCode_rationalSupportFloor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixSupportProductCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (rationalSupportFloor A) := by
  rw [machineMatrixSupportProductCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawRatRowsSupportProduct_eq_rationalSupportFloor]

end BeyondBethe
