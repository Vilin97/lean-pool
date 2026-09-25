/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineNearbyMatrixSum

/-!
# A directed upper logarithm sum for one matrix row

The four-core eligibility test repeatedly uses

`sum_k scheduledLogUpper (1 - X i k) p`.

This module realizes that row sum directly on the canonical optimizer word.
The input is `pair rowUnary optimizerWord`.  As in the matrix-wide nearby
sum, the transducer is total on arbitrary strings and clamps its unreduced
rational accumulator by an explicit degree-eight word.  The semantic proof
shows that the clamp is inactive on every canonical in-range row query.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineRowUpperPack
    (source current acc bound : List Bool) : List Bool :=
  pair source (pair current (pair acc bound))

def machineRowUpperSource (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRowUpperCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRowUpperAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineRowUpperBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineRowUpperRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRowUpperOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRowUpperMatrixWord (word : List Bool) : List Bool :=
  machineOptimizerMatrixWord (machineRowUpperOptimizerWord word)

def machineRowUpperInitialRow (word : List Bool) : List Bool :=
  machineListIndex
    (pair (machineRowUpperRowRuler word)
      (machineMatrixRowsWord (machineRowUpperMatrixWord word)))

def machineRowUpperEntry (state : List Bool) : List Bool :=
  machineListHead (machineRowUpperCurrent state)

def machineRowUpperComplementInput (state : List Bool) : List Bool :=
  pair
    (machineCertificateLogPrecisionRuler
      (machineRowUpperOptimizerWord (machineRowUpperSource state)))
    (pair (rawRatBinaryCode RawRat.zero) (machineRowUpperEntry state))

def machineRowUpperComplementCode (state : List Bool) : List Bool :=
  machineNearbyCoordinateComplementCode
    (machineRowUpperComplementInput state)

def machineRowUpperLogRawCode (state : List Bool) : List Bool :=
  machineScheduledLogUpperRawCode
    (pair
      (machineCertificateLogPrecisionRuler
        (machineRowUpperOptimizerWord (machineRowUpperSource state)))
      (machineRowUpperComplementCode state))

def machineRowUpperCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineRowUpperAcc state) (machineRowUpperLogRawCode state))

def machineRowUpperNextAcc (state : List Bool) : List Bool :=
  (machineRowUpperCandidate state).take (machineRowUpperBound state).length

def machineRowUpperStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRowUpperCurrent state) state
    (machineRowUpperPack
      (machineRowUpperSource state)
      (machineListTail (machineRowUpperCurrent state))
      (machineRowUpperNextAcc state)
      (machineRowUpperBound state))

def machineRowUpperInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth
    (machineBinaryMulWidth (machineBinaryMulWidth word))

def machineRowUpperInit (word : List Bool) : List Bool :=
  machineRowUpperPack word (machineRowUpperInitialRow word)
    (rawRatBinaryCode RawRat.zero) (machineRowUpperInputBound word)

def machineRowUpperWidth (word : List Bool) : List Bool :=
  let bound := machineRowUpperInputBound word
  machineRowUpperPack word word bound bound

def machineRowUpperFinalState (word : List Bool) : List Bool :=
  (machineRowUpperStep)^[word.length] (machineRowUpperInit word)

/-- Canonical raw-rational code for the directed upper complement-log row
sum, on every canonical in-range query. -/
def machineRowComplementUpperSumRawCode (word : List Bool) : List Bool :=
  machineRowUpperAcc (machineRowUpperFinalState word)

theorem machineRowUpperSource_mem_FP : machineRowUpperSource ∈ FP :=
  machinePairFirst_mem_FP

theorem machineRowUpperCurrent_mem_FP : machineRowUpperCurrent ∈ FP := by
  simpa only [machineRowUpperCurrent] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRowUpperAcc_mem_FP : machineRowUpperAcc ∈ FP := by
  simpa only [machineRowUpperAcc] using! machineCompose_mem_FP
    (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
    machinePairFirst_mem_FP

theorem machineRowUpperBound_mem_FP : machineRowUpperBound ∈ FP := by
  simpa only [machineRowUpperBound] using! machineCompose_mem_FP
    (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
    machinePairSecond_mem_FP

theorem machineRowUpperRowRuler_mem_FP : machineRowUpperRowRuler ∈ FP :=
  machinePairFirst_mem_FP

theorem machineRowUpperOptimizerWord_mem_FP :
    machineRowUpperOptimizerWord ∈ FP := machinePairSecond_mem_FP

theorem machineRowUpperMatrixWord_mem_FP : machineRowUpperMatrixWord ∈ FP := by
  simpa only [machineRowUpperMatrixWord] using! machineCompose_mem_FP
    machineRowUpperOptimizerWord_mem_FP machineOptimizerMatrixWord_mem_FP

theorem machineRowUpperInitialRow_mem_FP : machineRowUpperInitialRow ∈ FP := by
  have hrows := machineCompose_mem_FP machineRowUpperMatrixWord_mem_FP
    machineMatrixRowsWord_mem_FP
  have hpair := machinePair_mem_FP machineRowUpperRowRuler_mem_FP hrows
  simpa only [machineRowUpperInitialRow] using!
    machineCompose_mem_FP hpair machineListIndex_mem_FP

theorem machineRowUpperEntry_mem_FP : machineRowUpperEntry ∈ FP := by
  simpa only [machineRowUpperEntry] using! machineCompose_mem_FP
    machineRowUpperCurrent_mem_FP machineListHead_mem_FP

theorem machineRowUpperComplementInput_mem_FP :
    machineRowUpperComplementInput ∈ FP := by
  have hsourceOptimizer := machineCompose_mem_FP machineRowUpperSource_mem_FP
    machineRowUpperOptimizerWord_mem_FP
  have hp := machineCompose_mem_FP hsourceOptimizer
    machineCertificateLogPrecisionRuler_mem_FP
  exact machinePair_mem_FP hp
    (machinePair_mem_FP (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
      machineRowUpperEntry_mem_FP)

theorem machineRowUpperComplementCode_mem_FP :
    machineRowUpperComplementCode ∈ FP := by
  simpa only [machineRowUpperComplementCode] using! machineCompose_mem_FP
    machineRowUpperComplementInput_mem_FP
    machineNearbyCoordinateComplementCode_mem_FP

theorem machineRowUpperLogRawCode_mem_FP : machineRowUpperLogRawCode ∈ FP := by
  have hsourceOptimizer := machineCompose_mem_FP machineRowUpperSource_mem_FP
    machineRowUpperOptimizerWord_mem_FP
  have hp := machineCompose_mem_FP hsourceOptimizer
    machineCertificateLogPrecisionRuler_mem_FP
  have hpair := machinePair_mem_FP hp machineRowUpperComplementCode_mem_FP
  simpa only [machineRowUpperLogRawCode] using! machineCompose_mem_FP hpair
    machineScheduledLogUpperRawCode_mem_FP

theorem machineRowUpperCandidate_mem_FP : machineRowUpperCandidate ∈ FP := by
  have hpair := machinePair_mem_FP machineRowUpperAcc_mem_FP
    machineRowUpperLogRawCode_mem_FP
  simpa only [machineRowUpperCandidate] using! machineCompose_mem_FP hpair
    machineRawRatAddCode_mem_FP

theorem machineRowUpperNextAcc_mem_FP : machineRowUpperNextAcc ∈ FP := by
  simpa only [machineRowUpperNextAcc] using! machineTake_mem_FP
    machineRowUpperBound_mem_FP machineRowUpperCandidate_mem_FP

theorem machineRowUpperStep_mem_FP : machineRowUpperStep ∈ FP := by
  have htail := machineCompose_mem_FP machineRowUpperCurrent_mem_FP
    machineListTail_mem_FP
  have helse := machinePair_mem_FP machineRowUpperSource_mem_FP
    (machinePair_mem_FP htail
      (machinePair_mem_FP machineRowUpperNextAcc_mem_FP
        machineRowUpperBound_mem_FP))
  exact machineIfEmpty_mem_FP machineRowUpperCurrent_mem_FP id_mem_FP helse

theorem machineRowUpperInputBound_mem_FP : machineRowUpperInputBound ∈ FP := by
  have h1 := machineBinaryMulWidth_mem_FP
  have h2 := machineCompose_mem_FP h1 machineBinaryMulWidth_mem_FP
  simpa only [machineRowUpperInputBound] using!
    machineCompose_mem_FP h2 machineBinaryMulWidth_mem_FP

theorem machineRowUpperInit_mem_FP : machineRowUpperInit ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineRowUpperInitialRow_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
        machineRowUpperInputBound_mem_FP))

theorem machineRowUpperWidth_mem_FP : machineRowUpperWidth ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP machineRowUpperInputBound_mem_FP
        machineRowUpperInputBound_mem_FP))

@[simp] theorem machineRowUpperSource_pack (source current acc bound) :
    machineRowUpperSource (machineRowUpperPack source current acc bound) =
      source := by simp [machineRowUpperSource, machineRowUpperPack]

@[simp] theorem machineRowUpperCurrent_pack (source current acc bound) :
    machineRowUpperCurrent (machineRowUpperPack source current acc bound) =
      current := by simp [machineRowUpperCurrent, machineRowUpperPack]

@[simp] theorem machineRowUpperAcc_pack (source current acc bound) :
    machineRowUpperAcc (machineRowUpperPack source current acc bound) = acc := by
  simp [machineRowUpperAcc, machineRowUpperPack]

@[simp] theorem machineRowUpperBound_pack (source current acc bound) :
    machineRowUpperBound (machineRowUpperPack source current acc bound) =
      bound := by simp [machineRowUpperBound, machineRowUpperPack]

def MachineRowUpperStateBound (word state : List Bool) : Prop :=
  state = machineRowUpperPack (machineRowUpperSource state)
      (machineRowUpperCurrent state) (machineRowUpperAcc state)
      (machineRowUpperBound state) ∧
    machineRowUpperSource state = word ∧
    (machineRowUpperCurrent state).length ≤ word.length ∧
    (machineRowUpperAcc state).length ≤
      (machineRowUpperInputBound word).length ∧
    machineRowUpperBound state = machineRowUpperInputBound word

theorem machineRowUpperInit_bound (word : List Bool) :
    MachineRowUpperStateBound word (machineRowUpperInit word) := by
  simp only [MachineRowUpperStateBound, machineRowUpperInit,
    machineRowUpperSource_pack, machineRowUpperCurrent_pack,
    machineRowUpperAcc_pack, machineRowUpperBound_pack]
  refine ⟨trivial, trivial, ?_, ?_, trivial⟩
  · have hindex := machineListIndex_length_le_data
      (pair (machineRowUpperRowRuler word)
        (machineMatrixRowsWord (machineRowUpperMatrixWord word)))
    simp only [machineListIndexData, machinePairSecond_pair] at hindex
    exact hindex.trans
      ((machinePairSecond_length_le
          (machineRowUpperMatrixWord word)).trans
            ((machinePairFirst_length_le
              (machineRowUpperOptimizerWord word)).trans
                (machinePairSecond_length_le word)))
  · simp [machineRowUpperInputBound, machineBinaryMulWidth,
      rawRatBinaryCode, RawRat.zero, integerBinaryCode]
    nlinarith [sq_nonneg (word.length + 16)]

theorem machineRowUpperStep_bound {word state : List Bool}
    (hstate : MachineRowUpperStateBound word state) :
    MachineRowUpperStateBound word (machineRowUpperStep state) := by
  rcases hstate with ⟨hdecomp, hsource, hcurrent, hacc, hbound⟩
  by_cases hc : machineRowUpperCurrent state = []
  · rw [machineRowUpperStep, hc, machineIfEmpty_nil]
    exact ⟨hdecomp, hsource, hcurrent, hacc, hbound⟩
  · rw [machineRowUpperStep]
    cases hcode : machineRowUpperCurrent state with
    | nil => exact False.elim (hc hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons]
        simp only [MachineRowUpperStateBound,
          machineRowUpperSource_pack, machineRowUpperCurrent_pack,
          machineRowUpperAcc_pack, machineRowUpperBound_pack]
        refine ⟨trivial, hsource, ?_, ?_, hbound⟩
        · have htail := machineListTail_length_le
            (machineRowUpperCurrent state)
          rw [hcode] at htail
          rw [hcode] at hcurrent
          exact htail.trans hcurrent
        · rw [machineRowUpperNextAcc, hbound]
          exact List.length_take_le _ _

theorem machineRowUpperIterate_bound (word : List Bool) : ∀ k,
    MachineRowUpperStateBound word
      ((machineRowUpperStep)^[k] (machineRowUpperInit word)) := by
  intro k
  induction k with
  | zero => exact machineRowUpperInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRowUpperStep_bound ih

theorem machineRowUpperIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineRowUpperStep)^[iterations]
      (machineRowUpperInit word)).length ≤ (machineRowUpperWidth word).length := by
  rcases machineRowUpperIterate_bound word iterations with
    ⟨hdecomp, hsource, hcurrent, hacc, hbound⟩
  rw [hdecomp, hsource, hbound]
  simp only [machineRowUpperPack, machineRowUpperWidth, pair_length]
  omega

theorem machineRowUpperFinalState_mem_FP : machineRowUpperFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRowUpperStep_mem_FP
    machineRowUpperInit_mem_FP id_mem_FP machineRowUpperWidth_mem_FP
    machineRowUpperIterate_length_le_width

theorem machineRowComplementUpperSumRawCode_mem_FP :
    machineRowComplementUpperSumRawCode ∈ FP := by
  simpa only [machineRowComplementUpperSumRawCode] using! machineCompose_mem_FP
    machineRowUpperFinalState_mem_FP machineRowUpperAcc_mem_FP

/-! ## Exact semantics -/

def rawRowComplementUpperCost (p : ℕ) (xs : List ℚ) : ℕ :=
  (xs.map fun q => rawRatWidth (rawScheduledLogUpper (1 - q) p) + 1).sum

def rawRowComplementUpperSum (p : ℕ) : RawRat → List ℚ → RawRat
  | acc, [] => acc
  | acc, q :: qs =>
      rawRowComplementUpperSum p
        (acc.add (rawScheduledLogUpper (1 - q) p)) qs

structure RowUpperSemState where
  current : List ℚ
  acc : RawRat

def rowUpperSemStep (p : ℕ) (s : RowUpperSemState) : RowUpperSemState :=
  match s.current with
  | [] => s
  | q :: qs => ⟨qs, s.acc.add (rawScheduledLogUpper (1 - q) p)⟩

def rowUpperSemCode (source bound : List Bool)
    (s : RowUpperSemState) : List Bool :=
  machineRowUpperPack source
    (binaryListCode rationalEntryBinaryCode s.current)
    (rawRatBinaryCode s.acc) bound

def RowUpperSemInvariant (p budget : ℕ) (s : RowUpperSemState) : Prop :=
  rawRatWidth s.acc + rawRowComplementUpperCost p s.current ≤ budget

theorem rowUpperSemStep_invariant {p budget : ℕ} {s : RowUpperSemState}
    (hs : RowUpperSemInvariant p budget s) :
    RowUpperSemInvariant p budget (rowUpperSemStep p s) := by
  rcases s with ⟨current, acc⟩
  cases current with
  | nil => exact hs
  | cons q qs =>
      have hadd := rawRatWidth_add_le acc
        (rawScheduledLogUpper (1 - q) p)
      simp only [RowUpperSemInvariant, rowUpperSemStep,
        rawRowComplementUpperCost, List.map_cons, List.sum_cons] at hs ⊢
      omega

@[simp] theorem machineRowUpperInitialRow_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i : Fin n) :
    machineRowUpperInitialRow
        (pair (List.replicate i.1 true)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      binaryListCode rationalEntryBinaryCode (List.ofFn (X i)) := by
  rw [machineRowUpperInitialRow]
  simp only [machineRowUpperRowRuler, machinePairFirst_pair,
    machineRowUpperMatrixWord, machineRowUpperOptimizerWord,
    machinePairSecond_pair, machineOptimizerMatrixWord_encode,
    machineMatrixRowsWord_encode]
  rw [machineListIndex_binaryListCode]
  · simp [rationalMatrixRows, List.getElem_ofFn]
  · simp [rationalMatrixRows]

@[simp] theorem machineRowUpperComplementCode_semCode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rowRuler : List Bool) (q : ℚ) (qs : List ℚ) (acc : RawRat)
    (bound : List Bool) :
    machineRowUpperComplementCode
        (rowUpperSemCode
          (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound
          ⟨q :: qs, acc⟩) =
      rawRatBinaryCode (rawRatOfRat (1 - q)) := by
  rw [machineRowUpperComplementCode, machineRowUpperComplementInput]
  simp only [rowUpperSemCode, machineRowUpperSource_pack,
    machineRowUpperOptimizerWord, machinePairSecond_pair,
    machineCertificateLogPrecisionRuler_encode, machineRowUpperEntry,
    machineRowUpperCurrent_pack, machineListHead_cons,
    machineNearbyCoordinateComplementCode_encode]

@[simp] theorem machineRowUpperLogRawCode_semCode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rowRuler : List Bool) (q : ℚ) (qs : List ℚ) (acc : RawRat)
    (bound : List Bool) :
    machineRowUpperLogRawCode
        (rowUpperSemCode
          (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound
          ⟨q :: qs, acc⟩) =
      rawRatBinaryCode
        (rawScheduledLogUpper (1 - q) (directedCertificatePrecision n)) := by
  have hcomp := machineRowUpperComplementCode_semCode
    X R C rowRuler q qs acc bound
  dsimp only [rowUpperSemCode] at hcomp
  rw [machineRowUpperLogRawCode]
  simp only [rowUpperSemCode, machineRowUpperSource_pack,
    machineRowUpperOptimizerWord, machinePairSecond_pair,
    machineCertificateLogPrecisionRuler_encode]
  rw [hcomp, machineScheduledLogUpperRawCode_encode]

theorem machineRowUpperStep_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rowRuler bound : List Bool) (s : RowUpperSemState) (budget : ℕ)
    (hs : RowUpperSemInvariant (directedCertificatePrecision n) budget s)
    (hlarge : 4 + 3 * budget ≤ bound.length) :
    machineRowUpperStep
        (rowUpperSemCode
          (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound s) =
      rowUpperSemCode
        (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound
        (rowUpperSemStep (directedCertificatePrecision n) s) := by
  rcases s with ⟨current, acc⟩
  cases current with
  | nil =>
      simp [rowUpperSemCode, rowUpperSemStep, machineRowUpperStep,
        binaryListCode]
  | cons q qs =>
      have hlog := machineRowUpperLogRawCode_semCode
        X R C rowRuler q qs acc bound
      dsimp only [rowUpperSemCode] at hlog
      have hnext : rawRatWidth
          (acc.add (rawScheduledLogUpper (1 - q)
            (directedCertificatePrecision n))) ≤ budget := by
        have hinv := rowUpperSemStep_invariant hs
        have hinv' : rawRatWidth
            (acc.add (rawScheduledLogUpper (1 - q)
              (directedCertificatePrecision n))) +
            rawRowComplementUpperCost (directedCertificatePrecision n) qs ≤
              budget := by
          simpa only [RowUpperSemInvariant, rowUpperSemStep] using! hinv
        omega
      have hcode :
          (rawRatBinaryCode
            (acc.add (rawScheduledLogUpper (1 - q)
              (directedCertificatePrecision n)))).length ≤ bound.length :=
        (rawRatBinaryCode_length_le_width _).trans
          ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans hlarge)
      rw [rowUpperSemCode, rowUpperSemStep, machineRowUpperStep]
      simp only [machineRowUpperCurrent_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineRowUpperSource_pack, machineRowUpperCurrent_pack,
        machineRowUpperAcc_pack, machineRowUpperBound_pack,
        machineListTail_cons, machineRowUpperNextAcc,
        machineRowUpperCandidate]
      rw [hlog]
      rw [machineRawRatAddCode_encode]
      rw [(List.take_eq_self_iff _).mpr hcode]
      rfl

theorem machineRowUpperIterate_semantics {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rowRuler bound : List Bool) (s : RowUpperSemState) (budget : ℕ)
    (hs : RowUpperSemInvariant (directedCertificatePrecision n) budget s)
    (hlarge : 4 + 3 * budget ≤ bound.length) : ∀ k,
    (machineRowUpperStep)^[k]
        (rowUpperSemCode
          (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound s) =
      rowUpperSemCode
        (pair rowRuler (rationalOptimizerOutputCode ⟨X, R, C⟩)) bound
        ((rowUpperSemStep (directedCertificatePrecision n))^[k] s) := by
  intro k
  have hinv : ∀ t, RowUpperSemInvariant (directedCertificatePrecision n)
      budget ((rowUpperSemStep (directedCertificatePrecision n))^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact rowUpperSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineRowUpperStep_semantics X R C rowRuler bound _ budget
        (hinv k) hlarge

theorem rowUpperSem_processList (p : ℕ) (xs : List ℚ) (acc : RawRat) :
    (rowUpperSemStep p)^[xs.length] ⟨xs, acc⟩ =
      ⟨[], rawRowComplementUpperSum p acc xs⟩ := by
  induction xs generalizing acc with
  | nil => rfl
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        rowUpperSemStep, ih]
      rfl

theorem machineRowUpper_done_iterate
    (extra : ℕ) (source : List Bool) (acc : RawRat) (bound : List Bool) :
    (machineRowUpperStep)^[extra]
        (machineRowUpperPack source [] (rawRatBinaryCode acc) bound) =
      machineRowUpperPack source [] (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRowUpperStep]

def rawRowComplementUpperInputWidthBudget (L : ℕ) : ℕ :=
  64 * ((L + 400) + 2 * (44 + 12 * L) + 4) ^ 2 *
    ((44 + 12 * L) + 2)

theorem rawScheduledLogUpper_complement_width_le_query
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i j : Fin n) :
    rawRatWidth (rawScheduledLogUpper (1 - X i j)
        (directedCertificatePrecision n)) ≤
      rawRowComplementUpperInputWidthBudget
        (pair (List.replicate i.1 true)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)).length := by
  let optimizer := rationalOptimizerOutputCode ⟨X, R, C⟩
  let word := pair (List.replicate i.1 true) optimizer
  let L := word.length
  have hentryCode : (rationalEntryBinaryCode (X i j)).length ≤
      optimizer.length := by
    have hrow : List.ofFn (X i) ∈ rationalMatrixRows X := by
      simp [rationalMatrixRows]
    have hq : X i j ∈ List.ofFn (X i) := by simp
    have hqCode := binaryListCode_element_length_le rationalEntryBinaryCode hq
    have hrowCode := binaryListCode_element_length_le
      (binaryListCode rationalEntryBinaryCode) hrow
    have hrowsCode :
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows X)).length ≤ optimizer.length := by
      calc
        _ = (machineMatrixRowsWord
            (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)).length := by
          simpa using! congrArg List.length (machineMatrixRowsWord_encode X).symm
        _ ≤ (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length := by
          simpa only [machineMatrixRowsWord] using! machinePairSecond_length_le
            (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)
        _ ≤ optimizer.length := by
          simpa only [optimizer, rationalOptimizerOutputCode,
            machinePairFirst_pair] using! machinePairFirst_length_le optimizer
    exact hqCode.trans (hrowCode.trans hrowsCode)
  have hxWidth : rawRatWidth (rawRatOfRat (X i j)) ≤ L := by
    have hentryRaw :
        (rawRatBinaryCode (rawRatOfRat (X i j))).length ≤ optimizer.length := by
      simpa only [rawRatBinaryCode_rawRatOfRat] using! hentryCode
    have hoptimizerWord : optimizer.length ≤ word.length := by
      simpa only [word, machinePairSecond_pair] using!
        machinePairSecond_length_le word
    exact (rawRatWidth_le_binaryCode_length _).trans
      (hentryRaw.trans hoptimizerWord)
  have hcomp := rawRatWidth_complement_le (X i j)
  have hcompL : rawRatWidth (rawRatOfRat (1 - X i j)) ≤ 44 + 12 * L := by
    omega
  have hn := matrix_dimension_le_code_length X
  have hnL : n ≤ L := by
    have hmatrix :
        (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length ≤ optimizer.length := by
      simpa only [optimizer, rationalOptimizerOutputCode,
        machinePairFirst_pair] using! machinePairFirst_length_le optimizer
    have hoptimizerWord : optimizer.length ≤ word.length := by
      simpa only [word, machinePairSecond_pair] using!
        machinePairSecond_length_le word
    exact hn.trans (hmatrix.trans hoptimizerWord)
  have hp : directedCertificatePrecision n ≤ L + 400 := by
    rw [directedCertificatePrecision]
    omega
  simpa only [rawRowComplementUpperInputWidthBudget, L] using!
    rawRatWidth_scheduledLogUpper_of_bounds_le (1 - X i j) hp hcompL

theorem rawRowComplementUpperCost_le_query
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) :
    rawRowComplementUpperCost (directedCertificatePrecision n)
        (List.ofFn (X i)) ≤
      (pair (List.replicate i.1 true)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)).length *
        (rawRowComplementUpperInputWidthBudget
          (pair (List.replicate i.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩)).length + 1) := by
  let word := pair (List.replicate i.1 true)
    (rationalOptimizerOutputCode ⟨X, R, C⟩)
  let budget := rawRowComplementUpperInputWidthBudget word.length
  have hpoint : ∀ q ∈ List.ofFn (X i),
      rawRatWidth (rawScheduledLogUpper (1 - q)
        (directedCertificatePrecision n)) ≤ budget := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    simpa only [word, budget] using!
      rawScheduledLogUpper_complement_width_le_query X R C i j
  have rawCost_le_uniform : ∀ xs : List ℚ,
      (∀ q ∈ xs, rawRatWidth (rawScheduledLogUpper (1 - q)
        (directedCertificatePrecision n)) ≤ budget) →
      rawRowComplementUpperCost (directedCertificatePrecision n) xs ≤
        xs.length * (budget + 1) := by
    intro xs hxs
    induction xs with
    | nil => simp [rawRowComplementUpperCost]
    | cons q qs ih =>
        have hq := hxs q (by simp)
        have htail : ∀ r ∈ qs,
            rawRatWidth (rawScheduledLogUpper (1 - r)
              (directedCertificatePrecision n)) ≤ budget := by
          intro r hr
          exact hxs r (by simp [hr])
        have ih' := ih htail
        have ih'' :
            (qs.map fun r => rawRatWidth
              (rawScheduledLogUpper (1 - r)
                (directedCertificatePrecision n)) + 1).sum ≤
              qs.length * (budget + 1) := by
          simpa only [rawRowComplementUpperCost] using! ih'
        simp only [rawRowComplementUpperCost, List.map_cons, List.sum_cons,
          List.length_cons, Nat.add_mul]
        omega
  have hcost := rawCost_le_uniform (List.ofFn (X i)) hpoint
  have hn : (List.ofFn (X i)).length = n := by simp
  have hnword : n ≤ word.length := by
    have hnopt := matrix_dimension_le_code_length X
    have hmatrix :
        (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length ≤
          (rationalOptimizerOutputCode ⟨X, R, C⟩).length := by
      simpa only [rationalOptimizerOutputCode, machinePairFirst_pair] using!
        machinePairFirst_length_le
          (rationalOptimizerOutputCode ⟨X, R, C⟩)
    have hoptimizerWord :
        (rationalOptimizerOutputCode ⟨X, R, C⟩).length ≤ word.length := by
      simpa only [word, machinePairSecond_pair] using!
        machinePairSecond_length_le word
    exact hnopt.trans (hmatrix.trans hoptimizerWord)
  rw [hn] at hcost
  exact hcost.trans (Nat.mul_le_mul_right (budget + 1) hnword)

theorem machineRowUpperInputBound_length_dominates (word : List Bool) :
    4 + 3 * (1 + word.length *
      (rawRowComplementUpperInputWidthBudget word.length + 1)) ≤
        (machineRowUpperInputBound word).length := by
  have hnear := machineNearbyMatrixInputBound_length_dominates word
  have hbudget : rawRowComplementUpperInputWidthBudget word.length ≤
      rawNearbyCoordinateInputWidthBudget word.length := by
    simp only [rawRowComplementUpperInputWidthBudget,
      rawNearbyCoordinateInputWidthBudget]
    omega
  have hmul := Nat.mul_le_mul_left word.length
    (Nat.add_le_add_right hbudget 1)
  have htarget :
      4 + 3 * (1 + word.length *
        (rawRowComplementUpperInputWidthBudget word.length + 1)) ≤
      4 + 3 * (1 + word.length *
        (rawNearbyCoordinateInputWidthBudget word.length + 1)) := by omega
  simpa only [machineRowUpperInputBound, machineNearbyMatrixInputBound] using!
    htarget.trans hnear

@[simp] theorem machineRowComplementUpperSumRawCode_encode
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (i : Fin n) :
    machineRowComplementUpperSumRawCode
        (pair (List.replicate i.1 true)
          (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode
        (rawRowComplementUpperSum (directedCertificatePrecision n)
          RawRat.zero (List.ofFn (X i))) := by
  let word := pair (List.replicate i.1 true)
    (rationalOptimizerOutputCode ⟨X, R, C⟩)
  let xs := List.ofFn (X i)
  let p := directedCertificatePrecision n
  let s : RowUpperSemState := ⟨xs, RawRat.zero⟩
  let budget := 1 + rawRowComplementUpperCost p xs
  have hinv : RowUpperSemInvariant p budget s := by
    simp [RowUpperSemInvariant, s, budget, rawRatWidth_zero]
  have hrowCode : (binaryListCode rationalEntryBinaryCode xs).length ≤
      word.length := by
    calc
      _ = (machineRowUpperInitialRow word).length := by
        simpa only [word, xs] using! congrArg List.length
          (machineRowUpperInitialRow_encode X R C i).symm
      _ ≤ word.length := by
        have hindex := machineListIndex_length_le_data
          (pair (machineRowUpperRowRuler word)
            (machineMatrixRowsWord (machineRowUpperMatrixWord word)))
        simp only [machineListIndexData, machinePairSecond_pair] at hindex
        exact hindex.trans
          ((machinePairSecond_length_le
              (machineRowUpperMatrixWord word)).trans
                ((machinePairFirst_length_le
                  (machineRowUpperOptimizerWord word)).trans
                    (machinePairSecond_length_le word)))
  have hwork : xs.length ≤ word.length := by
    exact (list_length_le_binaryListCode_length
      rationalEntryBinaryCode xs).trans hrowCode
  have hsplit : word.length = (word.length - xs.length) + xs.length := by omega
  have hinit : machineRowUpperInit word =
      rowUpperSemCode word (machineRowUpperInputBound word) s := by
    simp [machineRowUpperInit, rowUpperSemCode, s, word, xs,
      machineRowUpperInitialRow_encode]
  have hcost := rawRowComplementUpperCost_le_query X R C i
  have hruler := machineRowUpperInputBound_length_dominates word
  have hlarge : 4 + 3 * budget ≤
      (machineRowUpperInputBound word).length := by
    have hbudget : budget ≤ 1 + word.length *
        (rawRowComplementUpperInputWidthBudget word.length + 1) := by
      dsimp only [budget, p, xs, word] at hcost ⊢
      omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hbudget) 4).trans
      hruler
  rw [machineRowComplementUpperSumRawCode, machineRowUpperFinalState,
    hsplit, Function.iterate_add_apply, hinit,
    machineRowUpperIterate_semantics X R C (List.replicate i.1 true)
      (machineRowUpperInputBound word) s budget hinv hlarge,
    rowUpperSem_processList]
  simp only [rowUpperSemCode, binaryListCode]
  rw [machineRowUpper_done_iterate]
  simp [machineRowUpperAcc_pack, xs]

theorem rawRowComplementUpperSum_value (p : ℕ) (acc : RawRat) : ∀ xs,
    (rawRowComplementUpperSum p acc xs).value =
      acc.value + (xs.map fun q => scheduledLogUpper (1 - q) p).sum := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRowComplementUpperSum]
  | cons q qs ih =>
      rw [rawRowComplementUpperSum, ih]
      simp [rawScheduledLogUpper_value, add_assoc]

theorem rawRowComplementUpperSum_matrix_value {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) (p : ℕ) :
    (rawRowComplementUpperSum p RawRat.zero (List.ofFn (X i))).value =
      ∑ k, scheduledLogUpper (1 - X i k) p := by
  rw [rawRowComplementUpperSum_value]
  simp [List.sum_ofFn]

end BeyondBethe
