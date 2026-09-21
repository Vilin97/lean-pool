/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixNonnegative

/-!
# Polynomial-time row-major rational matrix sum

The normalization scale starts with the sum of all matrix entries.  We scan
the canonical nested row code and accumulate an unreduced fraction.  A
quadratic clamp gives a global state envelope on malformed strings.  The
semantic width invariant below proves that the clamp is inactive on every
canonical matrix input.
-/

namespace BeyondBethe

open Complexity

def machineMatrixRawSumPack
    (rows current acc bound : List Bool) : List Bool :=
  pair rows (pair current (pair acc bound))

def machineMatrixRawSumRows (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMatrixRawSumCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMatrixRawSumAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineMatrixRawSumBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineMatrixRawSumEntry (state : List Bool) : List Bool :=
  machineListHead (machineMatrixRawSumCurrent state)

def machineMatrixRawSumCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineMatrixRawSumAcc state)
      (machineMatrixRawSumEntry state))

def machineMatrixRawSumNextAcc (state : List Bool) : List Bool :=
  (machineMatrixRawSumCandidate state).take
    (machineMatrixRawSumBound state).length

def machineMatrixRawSumProcessEntry (state : List Bool) : List Bool :=
  machineMatrixRawSumPack
    (machineMatrixRawSumRows state)
    (machineListTail (machineMatrixRawSumCurrent state))
    (machineMatrixRawSumNextAcc state)
    (machineMatrixRawSumBound state)

def machineMatrixRawSumLoadRow (state : List Bool) : List Bool :=
  machineMatrixRawSumPack
    (machineListTail (machineMatrixRawSumRows state))
    (machineListHead (machineMatrixRawSumRows state))
    (machineMatrixRawSumAcc state)
    (machineMatrixRawSumBound state)

def machineMatrixRawSumAfterRow (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixRawSumRows state) state
    (machineMatrixRawSumLoadRow state)

def machineMatrixRawSumStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixRawSumCurrent state)
    (machineMatrixRawSumAfterRow state)
    (machineMatrixRawSumProcessEntry state)

/-- A quadratic word used both as an accumulator clamp and a state envelope. -/
def machineMatrixRawSumInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineMatrixRawSumInit (word : List Bool) : List Bool :=
  machineMatrixRawSumPack (machineMatrixRowsWord word) []
    (rawRatBinaryCode RawRat.zero) (machineMatrixRawSumInputBound word)

def machineMatrixRawSumWidth (word : List Bool) : List Bool :=
  let bound := machineMatrixRawSumInputBound word
  machineMatrixRawSumPack word word bound bound

def machineMatrixRawSumFinalState (word : List Bool) : List Bool :=
  (machineMatrixRawSumStep)^[word.length] (machineMatrixRawSumInit word)

def machineMatrixRawSumCode (word : List Bool) : List Bool :=
  machineMatrixRawSumAcc (machineMatrixRawSumFinalState word)

def machineMatrixSumOutputCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineMatrixRawSumCode word)

/-- Unreduced code of `1 + sum A`, the normalization scale used later. -/
def machineMatrixNormalizationScaleRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode RawRat.one) (machineMatrixRawSumCode word))

def machineMatrixNormalizationScaleOutputCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode
    (machineMatrixNormalizationScaleRawCode word)

theorem machineMatrixRawSumRows_mem_FP :
    machineMatrixRawSumRows ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineMatrixRawSumCurrent_mem_FP :
    machineMatrixRawSumCurrent ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumCurrent] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatrixRawSumAcc_mem_FP :
    machineMatrixRawSumAcc ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumAcc] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineMatrixRawSumBound_mem_FP :
    machineMatrixRawSumBound ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumBound] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
      machinePairSecond_mem_FP

theorem machineMatrixRawSumEntry_mem_FP :
    machineMatrixRawSumEntry ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumEntry] using
    machineCompose_mem_FP machineMatrixRawSumCurrent_mem_FP
      machineListHead_mem_FP

theorem machineMatrixRawSumCandidate_mem_FP :
    machineMatrixRawSumCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixRawSumAcc_mem_FP
    machineMatrixRawSumEntry_mem_FP
  simpa only [machineMatrixRawSumCandidate] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineMatrixRawSumNextAcc_mem_FP :
    machineMatrixRawSumNextAcc ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumNextAcc] using
    machineTake_mem_FP machineMatrixRawSumBound_mem_FP
      machineMatrixRawSumCandidate_mem_FP

theorem machineMatrixRawSumProcessEntry_mem_FP :
    machineMatrixRawSumProcessEntry ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixRawSumCurrent_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP machineMatrixRawSumRows_mem_FP
    (machinePair_mem_FP htail
      (machinePair_mem_FP machineMatrixRawSumNextAcc_mem_FP
        machineMatrixRawSumBound_mem_FP))

theorem machineMatrixRawSumLoadRow_mem_FP :
    machineMatrixRawSumLoadRow ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixRawSumRows_mem_FP
    machineListTail_mem_FP
  have hhead := machineCompose_mem_FP machineMatrixRawSumRows_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP hhead
      (machinePair_mem_FP machineMatrixRawSumAcc_mem_FP
        machineMatrixRawSumBound_mem_FP))

theorem machineMatrixRawSumAfterRow_mem_FP :
    machineMatrixRawSumAfterRow ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixRawSumRows_mem_FP id_mem_FP
    machineMatrixRawSumLoadRow_mem_FP

theorem machineMatrixRawSumStep_mem_FP :
    machineMatrixRawSumStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixRawSumCurrent_mem_FP
    machineMatrixRawSumAfterRow_mem_FP machineMatrixRawSumProcessEntry_mem_FP

theorem machineMatrixRawSumInputBound_mem_FP :
    machineMatrixRawSumInputBound ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineMatrixRawSumInit_mem_FP :
    machineMatrixRawSumInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixRowsWord_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
        machineMatrixRawSumInputBound_mem_FP))

theorem machineMatrixRawSumWidth_mem_FP :
    machineMatrixRawSumWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineMatrixRawSumInputBound_mem_FP
        machineMatrixRawSumInputBound_mem_FP))

@[simp] theorem machineMatrixRawSumRows_pack (rows current acc bound) :
    machineMatrixRawSumRows
        (machineMatrixRawSumPack rows current acc bound) = rows := by
  simp [machineMatrixRawSumRows, machineMatrixRawSumPack]

@[simp] theorem machineMatrixRawSumCurrent_pack (rows current acc bound) :
    machineMatrixRawSumCurrent
        (machineMatrixRawSumPack rows current acc bound) = current := by
  simp [machineMatrixRawSumCurrent, machineMatrixRawSumPack]

@[simp] theorem machineMatrixRawSumAcc_pack (rows current acc bound) :
    machineMatrixRawSumAcc
        (machineMatrixRawSumPack rows current acc bound) = acc := by
  simp [machineMatrixRawSumAcc, machineMatrixRawSumPack]

@[simp] theorem machineMatrixRawSumBound_pack (rows current acc bound) :
    machineMatrixRawSumBound
        (machineMatrixRawSumPack rows current acc bound) = bound := by
  simp [machineMatrixRawSumBound, machineMatrixRawSumPack]

def MachineMatrixRawSumStateBound (word state : List Bool) : Prop :=
  state = machineMatrixRawSumPack
      (machineMatrixRawSumRows state) (machineMatrixRawSumCurrent state)
      (machineMatrixRawSumAcc state) (machineMatrixRawSumBound state) ∧
    (machineMatrixRawSumRows state).length ≤ word.length ∧
    (machineMatrixRawSumCurrent state).length ≤ word.length ∧
    (machineMatrixRawSumAcc state).length ≤
      (machineMatrixRawSumInputBound word).length ∧
    machineMatrixRawSumBound state = machineMatrixRawSumInputBound word

theorem machineMatrixRawSumInit_bound (word : List Bool) :
    MachineMatrixRawSumStateBound word (machineMatrixRawSumInit word) := by
  simp only [MachineMatrixRawSumStateBound, machineMatrixRawSumInit,
    machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
    machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineMatrixRowsWord] using machinePairSecond_length_le word
  · simp [machineMatrixRawSumInputBound, machineBinaryMulWidth,
      rawRatBinaryCode, RawRat.zero, integerBinaryCode]
    nlinarith [sq_nonneg (word.length + 16)]

theorem machineMatrixRawSumStep_bound {word state : List Bool}
    (hstate : MachineMatrixRawSumStateBound word state) :
    MachineMatrixRawSumStateBound word (machineMatrixRawSumStep state) := by
  rcases hstate with ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  by_cases hc : machineMatrixRawSumCurrent state = []
  · rw [machineMatrixRawSumStep, hc, machineIfEmpty_nil]
    by_cases hr : machineMatrixRawSumRows state = []
    · rw [machineMatrixRawSumAfterRow, hr, machineIfEmpty_nil]
      exact ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
    · rw [machineMatrixRawSumAfterRow]
      cases hrowsCode : machineMatrixRawSumRows state with
      | nil => exact False.elim (hr hrowsCode)
      | cons bit tail =>
          rw [machineIfEmpty_cons, machineMatrixRawSumLoadRow]
          simp only [MachineMatrixRawSumStateBound,
            machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
            machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
          refine ⟨trivial, ?_, ?_, hacc, hbound⟩
          · exact (machinePairSecond_length_le
              (machineMatrixRawSumRows state)).trans hrows
          · exact (machinePairFirst_length_le
              (machineMatrixRawSumRows state)).trans hrows
  · rw [machineMatrixRawSumStep]
    cases hcurrentCode : machineMatrixRawSumCurrent state with
    | nil => exact False.elim (hc hcurrentCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixRawSumProcessEntry]
        simp only [MachineMatrixRawSumStateBound,
          machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
          machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack]
        refine ⟨trivial, hrows, ?_, ?_, hbound⟩
        · exact (machinePairSecond_length_le
            (machineMatrixRawSumCurrent state)).trans hcurrent
        · rw [machineMatrixRawSumNextAcc, hbound]
          exact List.length_take_le _ _

theorem machineMatrixRawSumIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixRawSumStateBound word
      ((machineMatrixRawSumStep)^[k] (machineMatrixRawSumInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixRawSumInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixRawSumStep_bound ih

theorem machineMatrixRawSumIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineMatrixRawSumStep)^[iterations]
      (machineMatrixRawSumInit word)).length ≤
        (machineMatrixRawSumWidth word).length := by
  rcases machineMatrixRawSumIterate_bound word iterations with
    ⟨hdecomp, hrows, hcurrent, hacc, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineMatrixRawSumPack, machineMatrixRawSumWidth, pair_length]
  omega

theorem machineMatrixRawSumFinalState_mem_FP :
    machineMatrixRawSumFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixRawSumStep_mem_FP
    machineMatrixRawSumInit_mem_FP id_mem_FP machineMatrixRawSumWidth_mem_FP
    machineMatrixRawSumIterate_length_le_width

theorem machineMatrixRawSumCode_mem_FP :
    machineMatrixRawSumCode ∈ Complexity.FP := by
  simpa only [machineMatrixRawSumCode] using
    machineCompose_mem_FP machineMatrixRawSumFinalState_mem_FP
      machineMatrixRawSumAcc_mem_FP

theorem machineMatrixSumOutputCode_mem_FP :
    machineMatrixSumOutputCode ∈ Complexity.FP := by
  simpa only [machineMatrixSumOutputCode] using
    machineCompose_mem_FP machineMatrixRawSumCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineMatrixNormalizationScaleRawCode_mem_FP :
    machineMatrixNormalizationScaleRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineMatrixRawSumCode_mem_FP
  simpa only [machineMatrixNormalizationScaleRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineMatrixNormalizationScaleOutputCode_mem_FP :
    machineMatrixNormalizationScaleOutputCode ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizationScaleOutputCode] using
    machineCompose_mem_FP machineMatrixNormalizationScaleRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

/-! ## Semantic invariant and exactness -/

def rawRatListCost (xs : List ℚ) : ℕ :=
  (xs.map fun q => rawRatWidth (rawRatOfRat q) + 1).sum

def rawRatRowsCost (rows : List (List ℚ)) : ℕ :=
  (rows.map rawRatListCost).sum

def rawRatListSum : RawRat → List ℚ → RawRat
  | acc, [] => acc
  | acc, q :: qs => rawRatListSum (acc.add (rawRatOfRat q)) qs

def rawRatRowsSum : RawRat → List (List ℚ) → RawRat
  | acc, [] => acc
  | acc, row :: rows => rawRatRowsSum (rawRatListSum acc row) rows

theorem rawRatWidth_listSum_le (acc : RawRat) : ∀ xs : List ℚ,
    rawRatWidth (rawRatListSum acc xs) ≤ rawRatWidth acc + rawRatListCost xs := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListSum, rawRatListCost]
  | cons q qs ih =>
      rw [rawRatListSum]
      have hadd := rawRatWidth_add_le acc (rawRatOfRat q)
      have htail := ih (acc.add (rawRatOfRat q))
      simp only [rawRatListCost, List.map_cons, List.sum_cons] at htail ⊢
      omega

theorem rawRatWidth_rowsSum_le (acc : RawRat) : ∀ rows : List (List ℚ),
    rawRatWidth (rawRatRowsSum acc rows) ≤
      rawRatWidth acc + rawRatRowsCost rows := by
  intro rows
  induction rows generalizing acc with
  | nil => simp [rawRatRowsSum, rawRatRowsCost]
  | cons row rows ih =>
      rw [rawRatRowsSum]
      have hrow := rawRatWidth_listSum_le acc row
      have htail := ih (rawRatListSum acc row)
      simp only [rawRatRowsCost, List.map_cons, List.sum_cons] at htail ⊢
      omega

theorem integerNatAbs_size_le_binaryCode_length (z : ℤ) :
    z.natAbs.size ≤ (integerBinaryCode z).length := by
  cases z with
  | ofNat n =>
      simp [integerBinaryCode, Nat.size_eq_bits_len]
  | negSucc n =>
      have hs : (n + 1).size ≤ n.size + 1 := by
        rw [Nat.size_le]
        have hle : n + 1 ≤ 2 ^ n.size :=
          Nat.succ_le_iff.mpr (Nat.lt_size_self n)
        have hlt : 2 ^ n.size < 2 ^ (n.size + 1) := by
          rw [pow_succ]
          have hpos : 0 < 2 ^ n.size := by positivity
          omega
        exact hle.trans_lt hlt
      simpa [integerBinaryCode, Nat.size_eq_bits_len,
        Nat.add_comm] using hs

theorem rawRatWidth_le_binaryCode_length (q : RawRat) :
    rawRatWidth q ≤ (rawRatBinaryCode q).length := by
  rw [rawRatWidth, rawRatBinaryCode, pair_length]
  apply max_le
  · have h := integerNatAbs_size_le_binaryCode_length q.num
    omega
  · rw [Nat.size_eq_bits_len]
    omega

theorem rawRatBinaryCode_length_le_width (q : RawRat) :
    (rawRatBinaryCode q).length ≤ 4 + 3 * rawRatWidth q := by
  rw [rawRatBinaryCode, pair_length]
  have hnum : (integerBinaryCode q.num).length ≤ 1 + rawRatWidth q := by
    cases hqnum : q.num with
    | ofNat n =>
        simp only [integerBinaryCode, List.length_cons,
          Nat.size_eq_bits_len]
        have habs := rawRat_num_size_le_width q
        simp only [hqnum, Int.natAbs_ofNat'] at habs
        omega
    | negSucc n =>
        simp only [integerBinaryCode, List.length_cons,
          Nat.size_eq_bits_len]
        have hsize : n.size ≤ (n + 1).size :=
          Nat.size_le_size (Nat.le_succ n)
        have habs : (n + 1).size ≤ rawRatWidth q := by
          simpa only [hqnum, Int.natAbs_negSucc] using
            rawRat_num_size_le_width q
        omega
  have hden := rawRat_den_size_le_width q
  have hdenBits : q.den.bits.length ≤ rawRatWidth q := by
    rw [Nat.size_eq_bits_len]
    exact hden
  omega

/-- The ordinary finite-word encoding of an explicitly normalized rational
has length linear in the width of the unreduced input.  This is the bridge
between the exact `DataEncode` estimate used by the arithmetic analysis and
the concrete binary words carried by the machine implementation. -/
theorem rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
    (q : RawRat) :
    (rationalEntryBinaryCode (binaryNormalizeRawRat q)).length ≤
      64 + 36 * rawRatWidth q := by
  rw [← rawRatBinaryCode_rawRatOfRat]
  have hcode := rawRatBinaryCode_length_le_width
    (rawRatOfRat (binaryNormalizeRawRat q))
  have hwidth := rawRatOfRat_width_le_encodedBitLength
    (binaryNormalizeRawRat q)
  have hnormalize := binaryNormalizeRawRat_encodedBitLength_le q
  omega

theorem rawRatListCost_le_codeLength (xs : List ℚ) :
    rawRatListCost xs ≤ (binaryListCode rationalEntryBinaryCode xs).length := by
  induction xs with
  | nil => simp [rawRatListCost, binaryListCode]
  | cons q qs ih =>
      rw [rawRatListCost, List.map_cons, List.sum_cons,
        binaryListCode, pair_length]
      have ih' : (qs.map fun q => rawRatWidth (rawRatOfRat q) + 1).sum ≤
          (binaryListCode rationalEntryBinaryCode qs).length := by
        simpa only [rawRatListCost] using ih
      have hq : rawRatWidth (rawRatOfRat q) ≤
          (rationalEntryBinaryCode q).length := by
        rw [← rawRatBinaryCode_rawRatOfRat]
        exact rawRatWidth_le_binaryCode_length _
      omega

theorem rawRatRowsCost_le_codeLength (rows : List (List ℚ)) :
    rawRatRowsCost rows ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  induction rows with
  | nil => simp [rawRatRowsCost, binaryListCode]
  | cons row rows ih =>
      rw [rawRatRowsCost, List.map_cons, List.sum_cons,
        binaryListCode, pair_length]
      have ih' : (rows.map rawRatListCost).sum ≤
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
        simpa only [rawRatRowsCost] using ih
      have hrow := rawRatListCost_le_codeLength row
      omega

structure MatrixRawSumSemState where
  rows : List (List ℚ)
  current : List ℚ
  acc : RawRat

def matrixRawSumSemStep (s : MatrixRawSumSemState) : MatrixRawSumSemState :=
  match s.current with
  | q :: qs => ⟨s.rows, qs, s.acc.add (rawRatOfRat q)⟩
  | [] =>
      match s.rows with
      | row :: rows => ⟨rows, row, s.acc⟩
      | [] => s

def matrixRawSumSemCode (bound : List Bool)
    (s : MatrixRawSumSemState) : List Bool :=
  machineMatrixRawSumPack
    (binaryListCode (binaryListCode rationalEntryBinaryCode) s.rows)
    (binaryListCode rationalEntryBinaryCode s.current)
    (rawRatBinaryCode s.acc) bound

def MatrixRawSumSemInvariant (budget : ℕ)
    (s : MatrixRawSumSemState) : Prop :=
  rawRatWidth s.acc + rawRatListCost s.current + rawRatRowsCost s.rows ≤ budget

theorem matrixRawSumSemStep_invariant {budget : ℕ}
    {s : MatrixRawSumSemState} (hs : MatrixRawSumSemInvariant budget s) :
    MatrixRawSumSemInvariant budget (matrixRawSumSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil => exact hs
      | cons row rows =>
          simp [MatrixRawSumSemInvariant, matrixRawSumSemStep,
            rawRatRowsCost, rawRatListCost] at hs ⊢
          omega
  | cons q qs =>
      have hadd := rawRatWidth_add_le acc (rawRatOfRat q)
      simp only [MatrixRawSumSemInvariant, matrixRawSumSemStep,
        rawRatListCost, List.map_cons, List.sum_cons] at hs ⊢
      omega

theorem matrixRawSumBound_large (word : List Bool) :
    4 + 3 * (1 + word.length) ≤
      (machineMatrixRawSumInputBound word).length := by
  simp only [machineMatrixRawSumInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineMatrixRawSumStep_semantics
    (word : List Bool) (s : MatrixRawSumSemState)
    (hs : MatrixRawSumSemInvariant (1 + word.length) s) :
    machineMatrixRawSumStep
        (matrixRawSumSemCode (machineMatrixRawSumInputBound word) s) =
      matrixRawSumSemCode (machineMatrixRawSumInputBound word)
        (matrixRawSumSemStep s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil =>
          simp [matrixRawSumSemCode, matrixRawSumSemStep,
            machineMatrixRawSumStep, machineMatrixRawSumAfterRow,
            binaryListCode]
      | cons row rows =>
          rw [matrixRawSumSemCode, matrixRawSumSemStep,
            machineMatrixRawSumStep]
          simp only [machineMatrixRawSumCurrent_pack, binaryListCode,
            machineIfEmpty_nil, machineMatrixRawSumAfterRow,
            machineMatrixRawSumRows_pack]
          have hpair : pair (binaryListCode rationalEntryBinaryCode row)
              (binaryListCode (binaryListCode rationalEntryBinaryCode) rows) ≠ [] := by
            intro h
            have hlen := congrArg List.length h
            simp at hlen
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hpair]
          simp [machineMatrixRawSumLoadRow, matrixRawSumSemCode,
            machineListHead, machineListTail]
  | cons q qs =>
      have hnext : rawRatWidth (acc.add (rawRatOfRat q)) ≤ 1 + word.length := by
        have hinv := matrixRawSumSemStep_invariant hs
        have hinv' : rawRatWidth (acc.add (rawRatOfRat q)) +
            rawRatListCost qs + rawRatRowsCost rows ≤ 1 + word.length := by
          simpa only [MatrixRawSumSemInvariant, matrixRawSumSemStep] using hinv
        omega
      have hcode :
          (rawRatBinaryCode (acc.add (rawRatOfRat q))).length ≤
            (machineMatrixRawSumInputBound word).length :=
        (rawRatBinaryCode_length_le_width _).trans
          ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans
            (matrixRawSumBound_large word))
      rw [matrixRawSumSemCode, matrixRawSumSemStep,
        machineMatrixRawSumStep]
      simp only [machineMatrixRawSumCurrent_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineMatrixRawSumProcessEntry,
        machineMatrixRawSumRows_pack, machineMatrixRawSumCurrent_pack,
        machineMatrixRawSumAcc_pack, machineMatrixRawSumBound_pack,
        machineListTail_cons, machineMatrixRawSumNextAcc,
        machineMatrixRawSumCandidate, machineMatrixRawSumEntry,
        machineListHead_cons]
      rw [← rawRatBinaryCode_rawRatOfRat q,
        machineRawRatAddCode_encode]
      rw [(List.take_eq_self_iff _).mpr hcode]
      rfl

theorem machineMatrixRawSumIterate_semantics
    (word : List Bool) (s : MatrixRawSumSemState)
    (hs : MatrixRawSumSemInvariant (1 + word.length) s) : ∀ k,
    (machineMatrixRawSumStep)^[k]
        (matrixRawSumSemCode (machineMatrixRawSumInputBound word) s) =
      matrixRawSumSemCode (machineMatrixRawSumInputBound word)
        ((matrixRawSumSemStep)^[k] s) := by
  intro k
  have hinv : ∀ t : ℕ,
      MatrixRawSumSemInvariant (1 + word.length)
        ((matrixRawSumSemStep)^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact matrixRawSumSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineMatrixRawSumStep_semantics word _ (hinv k)

theorem matrixRawSumSem_processRow
    (rows : List (List ℚ)) (row : List ℚ) (acc : RawRat) :
    (matrixRawSumSemStep)^[row.length]
        ⟨rows, row, acc⟩ = ⟨rows, [], rawRatListSum acc row⟩ := by
  induction row generalizing acc with
  | nil => rfl
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        matrixRawSumSemStep, ih]
      rfl

theorem matrixRawSumSem_processRows
    (rows : List (List ℚ)) (acc : RawRat) :
    (matrixRawSumSemStep)^[matrixNonnegativeRowsWork rows]
        ⟨rows, [], acc⟩ = ⟨[], [], rawRatRowsSum acc rows⟩ := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rows ih =>
      rw [matrixNonnegativeRowsWork, show 1 + row.length +
          matrixNonnegativeRowsWork rows =
          matrixNonnegativeRowsWork rows + row.length + 1 by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, matrixRawSumSemStep,
        matrixRawSumSem_processRow, ih, rawRatRowsSum]

theorem matrixRawSumSem_done_iterate (extra : ℕ) (acc : RawRat) :
    (matrixRawSumSemStep)^[extra] ⟨[], [], acc⟩ = ⟨[], [], acc⟩ := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem machineMatrixRawSum_done_iterate
    (extra : ℕ) (acc : RawRat) (bound : List Bool) :
    (machineMatrixRawSumStep)^[extra]
        (machineMatrixRawSumPack [] [] (rawRatBinaryCode acc) bound) =
      machineMatrixRawSumPack [] [] (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineMatrixRawSumStep, machineMatrixRawSumAfterRow]

theorem machineMatrixRawSumFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixRawSumFinalState
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      machineMatrixRawSumPack [] []
        (rawRatBinaryCode
          (rawRatRowsSum RawRat.zero (rationalMatrixRows A)))
        (machineMatrixRawSumInputBound
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) := by
  let rows := rationalMatrixRows A
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let s : MatrixRawSumSemState := ⟨rows, [], RawRat.zero⟩
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
  have hinv : MatrixRawSumSemInvariant (1 + word.length) s := by
    simp only [MatrixRawSumSemInvariant, s, rawRatListCost,
      List.map_nil, List.sum_nil, rawRatWidth_zero, Nat.add_zero]
    exact Nat.add_le_add_left
      ((rawRatRowsCost_le_codeLength rows).trans hrowsLength) 1
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsLength
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  have hinit : machineMatrixRawSumInit word =
      matrixRawSumSemCode (machineMatrixRawSumInputBound word) s := by
    simp [machineMatrixRawSumInit, matrixRawSumSemCode, s, word, rows,
      binaryListCode]
  change machineMatrixRawSumFinalState word = _
  rw [machineMatrixRawSumFinalState, hsplit, Function.iterate_add_apply,
    hinit, machineMatrixRawSumIterate_semantics word s hinv,
    matrixRawSumSem_processRows]
  simp only [matrixRawSumSemCode, binaryListCode]
  rw [machineMatrixRawSum_done_iterate]

@[simp] theorem machineMatrixRawSumCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixRawSumCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawRatRowsSum RawRat.zero (rationalMatrixRows A)) := by
  rw [machineMatrixRawSumCode, machineMatrixRawSumFinalState_encode]
  simp

theorem rawRatListSum_value (acc : RawRat) : ∀ xs : List ℚ,
    (rawRatListSum acc xs).value = acc.value + xs.sum := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListSum]
  | cons q qs ih =>
      rw [rawRatListSum, ih]
      simp [rawRatOfRat_value, add_assoc]

theorem rawRatRowsSum_value (acc : RawRat) : ∀ rows : List (List ℚ),
    (rawRatRowsSum acc rows).value =
      acc.value + (rows.map List.sum).sum := by
  intro rows
  induction rows generalizing acc with
  | nil => simp [rawRatRowsSum]
  | cons row rows ih =>
      rw [rawRatRowsSum, ih, rawRatListSum_value]
      simp [add_assoc]

theorem rationalMatrixRows_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ((rationalMatrixRows A).map List.sum).sum =
      ∑ i, ∑ j, A i j := by
  simp [rationalMatrixRows, List.sum_ofFn]

@[simp] theorem machineMatrixSumOutputCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixSumOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (∑ i, ∑ j, A i j) := by
  rw [machineMatrixSumOutputCode, machineMatrixRawSumCode_encode,
    machineNormalizeRawRatBinaryCode_encode, binaryNormalizeRawRat_eq_value,
    rawRatRowsSum_value, RawRat.value_zero, zero_add,
    rationalMatrixRows_sum]

@[simp] theorem machineMatrixNormalizationScaleRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScaleRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (RawRat.one.add
          (rawRatRowsSum RawRat.zero (rationalMatrixRows A))) := by
  rw [machineMatrixNormalizationScaleRawCode,
    machineMatrixRawSumCode_encode, machineRawRatAddCode_encode]

@[simp] theorem machineMatrixNormalizationScaleOutputCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScaleOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (1 + ∑ i, ∑ j, A i j) := by
  rw [machineMatrixNormalizationScaleOutputCode,
    machineMatrixNormalizationScaleRawCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_add,
    RawRat.value_one, rawRatRowsSum_value, RawRat.value_zero,
    zero_add, rationalMatrixRows_sum]

end BeyondBethe
