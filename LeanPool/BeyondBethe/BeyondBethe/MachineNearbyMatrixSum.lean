/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledLogWidth

/-!
# Row-major evaluation of the nearby-Bethe coordinate sum

This module scans the matrix carried by a canonical optimizer-output word and
accumulates

`sum_ij directedNearbyCoordinateLower tau X_ij p`.

The concrete transducer is total on arbitrary bitstrings.  Its raw rational
accumulator is clamped by an explicit iterated-quadratic word; the semantic
section proves separately that this clamp is inactive on canonical inputs.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineNearbyMatrixPack
    (source rows current acc bound : List Bool) : List Bool :=
  pair source (pair rows (pair current (pair acc bound)))

def machineNearbyMatrixSource (state : List Bool) : List Bool :=
  machinePairFirst state

def machineNearbyMatrixRows (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineNearbyMatrixCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineNearbyMatrixAcc (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineNearbyMatrixBound (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineNearbyMatrixEntry (state : List Bool) : List Bool :=
  machineListHead (machineNearbyMatrixCurrent state)

def machineNearbyMatrixCoordinateInput (state : List Bool) : List Bool :=
  pair
    (machineCertificateLogPrecisionRuler (machineNearbyMatrixSource state))
    (pair
      (machineCertificateRegularizationScaleRawCode
        (machineNearbyMatrixSource state))
      (machineNearbyMatrixEntry state))

def machineNearbyMatrixCoordinateRawCode (state : List Bool) : List Bool :=
  machineNearbyCoordinateLowerRawCode
    (machineNearbyMatrixCoordinateInput state)

def machineNearbyMatrixCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineNearbyMatrixAcc state)
      (machineNearbyMatrixCoordinateRawCode state))

def machineNearbyMatrixNextAcc (state : List Bool) : List Bool :=
  (machineNearbyMatrixCandidate state).take
    (machineNearbyMatrixBound state).length

def machineNearbyMatrixProcessEntry (state : List Bool) : List Bool :=
  machineNearbyMatrixPack
    (machineNearbyMatrixSource state)
    (machineNearbyMatrixRows state)
    (machineListTail (machineNearbyMatrixCurrent state))
    (machineNearbyMatrixNextAcc state)
    (machineNearbyMatrixBound state)

def machineNearbyMatrixLoadRow (state : List Bool) : List Bool :=
  machineNearbyMatrixPack
    (machineNearbyMatrixSource state)
    (machineListTail (machineNearbyMatrixRows state))
    (machineListHead (machineNearbyMatrixRows state))
    (machineNearbyMatrixAcc state)
    (machineNearbyMatrixBound state)

def machineNearbyMatrixAfterRow (state : List Bool) : List Bool :=
  machineIfEmpty (machineNearbyMatrixRows state) state
    (machineNearbyMatrixLoadRow state)

def machineNearbyMatrixStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineNearbyMatrixCurrent state)
    (machineNearbyMatrixAfterRow state)
    (machineNearbyMatrixProcessEntry state)

/-- An explicit degree-eight accumulator envelope.  Repeated application of
`machineBinaryMulWidth` is a concrete finite-word construction, not an
existential polynomial ruler. -/
def machineNearbyMatrixInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth
    (machineBinaryMulWidth (machineBinaryMulWidth word))

def machineNearbyMatrixRowsWord (word : List Bool) : List Bool :=
  machineMatrixRowsWord (machineOptimizerMatrixWord word)

def machineNearbyMatrixInit (word : List Bool) : List Bool :=
  machineNearbyMatrixPack word (machineNearbyMatrixRowsWord word) []
    (rawRatBinaryCode RawRat.zero) (machineNearbyMatrixInputBound word)

def machineNearbyMatrixWidth (word : List Bool) : List Bool :=
  let bound := machineNearbyMatrixInputBound word
  machineNearbyMatrixPack word word word bound bound

def machineNearbyMatrixFinalState (word : List Bool) : List Bool :=
  (machineNearbyMatrixStep)^[word.length] (machineNearbyMatrixInit word)

def machineNearbyMatrixRawSumCode (word : List Bool) : List Bool :=
  machineNearbyMatrixAcc (machineNearbyMatrixFinalState word)

theorem machineNearbyMatrixSource_mem_FP :
    machineNearbyMatrixSource ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineNearbyMatrixRows_mem_FP :
    machineNearbyMatrixRows ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixRows] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineNearbyMatrixCurrent_mem_FP :
    machineNearbyMatrixCurrent ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixCurrent] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineNearbyMatrixAcc_mem_FP :
    machineNearbyMatrixAcc ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixAcc] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP
        (machineCompose_mem_FP machinePairSecond_mem_FP
          machinePairSecond_mem_FP)
        machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineNearbyMatrixBound_mem_FP :
    machineNearbyMatrixBound ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixBound] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP
        (machineCompose_mem_FP machinePairSecond_mem_FP
          machinePairSecond_mem_FP)
        machinePairSecond_mem_FP)
      machinePairSecond_mem_FP

theorem machineNearbyMatrixEntry_mem_FP :
    machineNearbyMatrixEntry ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixEntry] using!
    machineCompose_mem_FP machineNearbyMatrixCurrent_mem_FP
      machineListHead_mem_FP

theorem machineNearbyMatrixCoordinateInput_mem_FP :
    machineNearbyMatrixCoordinateInput ∈ Complexity.FP := by
  have hp := machineCompose_mem_FP machineNearbyMatrixSource_mem_FP
    machineCertificateLogPrecisionRuler_mem_FP
  have htau := machineCompose_mem_FP machineNearbyMatrixSource_mem_FP
    machineCertificateRegularizationScaleRawCode_mem_FP
  exact machinePair_mem_FP hp
    (machinePair_mem_FP htau machineNearbyMatrixEntry_mem_FP)

theorem machineNearbyMatrixCoordinateRawCode_mem_FP :
    machineNearbyMatrixCoordinateRawCode ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixCoordinateRawCode] using!
    machineCompose_mem_FP machineNearbyMatrixCoordinateInput_mem_FP
      machineNearbyCoordinateLowerRawCode_mem_FP

theorem machineNearbyMatrixCandidate_mem_FP :
    machineNearbyMatrixCandidate ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineNearbyMatrixAcc_mem_FP
    machineNearbyMatrixCoordinateRawCode_mem_FP
  simpa only [machineNearbyMatrixCandidate] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineNearbyMatrixNextAcc_mem_FP :
    machineNearbyMatrixNextAcc ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixNextAcc] using!
    machineTake_mem_FP machineNearbyMatrixBound_mem_FP
      machineNearbyMatrixCandidate_mem_FP

theorem machineNearbyMatrixProcessEntry_mem_FP :
    machineNearbyMatrixProcessEntry ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineNearbyMatrixCurrent_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP machineNearbyMatrixSource_mem_FP
    (machinePair_mem_FP machineNearbyMatrixRows_mem_FP
      (machinePair_mem_FP htail
        (machinePair_mem_FP machineNearbyMatrixNextAcc_mem_FP
          machineNearbyMatrixBound_mem_FP)))

theorem machineNearbyMatrixLoadRow_mem_FP :
    machineNearbyMatrixLoadRow ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineNearbyMatrixRows_mem_FP
    machineListTail_mem_FP
  have hhead := machineCompose_mem_FP machineNearbyMatrixRows_mem_FP
    machineListHead_mem_FP
  exact machinePair_mem_FP machineNearbyMatrixSource_mem_FP
    (machinePair_mem_FP htail
      (machinePair_mem_FP hhead
        (machinePair_mem_FP machineNearbyMatrixAcc_mem_FP
          machineNearbyMatrixBound_mem_FP)))

theorem machineNearbyMatrixAfterRow_mem_FP :
    machineNearbyMatrixAfterRow ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineNearbyMatrixRows_mem_FP id_mem_FP
    machineNearbyMatrixLoadRow_mem_FP

theorem machineNearbyMatrixStep_mem_FP :
    machineNearbyMatrixStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineNearbyMatrixCurrent_mem_FP
    machineNearbyMatrixAfterRow_mem_FP machineNearbyMatrixProcessEntry_mem_FP

theorem machineNearbyMatrixInputBound_mem_FP :
    machineNearbyMatrixInputBound ∈ Complexity.FP := by
  have h1 := machineBinaryMulWidth_mem_FP
  have h2 := machineCompose_mem_FP h1 machineBinaryMulWidth_mem_FP
  simpa only [machineNearbyMatrixInputBound] using!
    machineCompose_mem_FP h2 machineBinaryMulWidth_mem_FP

theorem machineNearbyMatrixRowsWord_mem_FP :
    machineNearbyMatrixRowsWord ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixRowsWord] using!
    machineCompose_mem_FP machineOptimizerMatrixWord_mem_FP
      machineMatrixRowsWord_mem_FP

theorem machineNearbyMatrixInit_mem_FP :
    machineNearbyMatrixInit ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineNearbyMatrixRowsWord_mem_FP
      (machinePair_mem_FP (machineConst_mem_FP [])
        (machinePair_mem_FP
          (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
          machineNearbyMatrixInputBound_mem_FP)))

theorem machineNearbyMatrixWidth_mem_FP :
    machineNearbyMatrixWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP id_mem_FP
        (machinePair_mem_FP machineNearbyMatrixInputBound_mem_FP
          machineNearbyMatrixInputBound_mem_FP)))

@[simp] theorem machineNearbyMatrixSource_pack (source rows current acc bound) :
    machineNearbyMatrixSource
        (machineNearbyMatrixPack source rows current acc bound) = source := by
  simp [machineNearbyMatrixSource, machineNearbyMatrixPack]

@[simp] theorem machineNearbyMatrixRows_pack (source rows current acc bound) :
    machineNearbyMatrixRows
        (machineNearbyMatrixPack source rows current acc bound) = rows := by
  simp [machineNearbyMatrixRows, machineNearbyMatrixPack]

@[simp] theorem machineNearbyMatrixCurrent_pack
    (source rows current acc bound) :
    machineNearbyMatrixCurrent
        (machineNearbyMatrixPack source rows current acc bound) = current := by
  simp [machineNearbyMatrixCurrent, machineNearbyMatrixPack]

@[simp] theorem machineNearbyMatrixAcc_pack (source rows current acc bound) :
    machineNearbyMatrixAcc
        (machineNearbyMatrixPack source rows current acc bound) = acc := by
  simp [machineNearbyMatrixAcc, machineNearbyMatrixPack]

@[simp] theorem machineNearbyMatrixBound_pack (source rows current acc bound) :
    machineNearbyMatrixBound
        (machineNearbyMatrixPack source rows current acc bound) = bound := by
  simp [machineNearbyMatrixBound, machineNearbyMatrixPack]

def MachineNearbyMatrixStateBound (word state : List Bool) : Prop :=
  state = machineNearbyMatrixPack
      (machineNearbyMatrixSource state) (machineNearbyMatrixRows state)
      (machineNearbyMatrixCurrent state) (machineNearbyMatrixAcc state)
      (machineNearbyMatrixBound state) ∧
    machineNearbyMatrixSource state = word ∧
    (machineNearbyMatrixRows state).length ≤ word.length ∧
    (machineNearbyMatrixCurrent state).length ≤ word.length ∧
    (machineNearbyMatrixAcc state).length ≤
      (machineNearbyMatrixInputBound word).length ∧
    machineNearbyMatrixBound state = machineNearbyMatrixInputBound word

theorem machineNearbyMatrixInit_bound (word : List Bool) :
    MachineNearbyMatrixStateBound word (machineNearbyMatrixInit word) := by
  simp only [MachineNearbyMatrixStateBound, machineNearbyMatrixInit,
    machineNearbyMatrixSource_pack, machineNearbyMatrixRows_pack,
    machineNearbyMatrixCurrent_pack, machineNearbyMatrixAcc_pack,
    machineNearbyMatrixBound_pack]
  refine ⟨trivial, trivial, ?_, by simp, ?_, trivial⟩
  · exact (machinePairSecond_length_le
      (machineOptimizerMatrixWord word)).trans
        ((machinePairFirst_length_le word))
  · simp [machineNearbyMatrixInputBound, machineBinaryMulWidth,
      rawRatBinaryCode, RawRat.zero, integerBinaryCode]
    nlinarith [sq_nonneg (word.length + 16)]

theorem machineNearbyMatrixStep_bound {word state : List Bool}
    (hstate : MachineNearbyMatrixStateBound word state) :
    MachineNearbyMatrixStateBound word (machineNearbyMatrixStep state) := by
  rcases hstate with
    ⟨hdecomp, hsource, hrows, hcurrent, hacc, hbound⟩
  by_cases hc : machineNearbyMatrixCurrent state = []
  · rw [machineNearbyMatrixStep, hc, machineIfEmpty_nil]
    by_cases hr : machineNearbyMatrixRows state = []
    · rw [machineNearbyMatrixAfterRow, hr, machineIfEmpty_nil]
      exact ⟨hdecomp, hsource, hrows, hcurrent, hacc, hbound⟩
    · rw [machineNearbyMatrixAfterRow]
      cases hrowsCode : machineNearbyMatrixRows state with
      | nil => exact False.elim (hr hrowsCode)
      | cons bit tail =>
          rw [machineIfEmpty_cons, machineNearbyMatrixLoadRow]
          simp only [MachineNearbyMatrixStateBound,
            machineNearbyMatrixSource_pack, machineNearbyMatrixRows_pack,
            machineNearbyMatrixCurrent_pack, machineNearbyMatrixAcc_pack,
            machineNearbyMatrixBound_pack]
          refine ⟨trivial, hsource, ?_, ?_, hacc, hbound⟩
          · exact (machinePairSecond_length_le
              (machineNearbyMatrixRows state)).trans hrows
          · exact (machinePairFirst_length_le
              (machineNearbyMatrixRows state)).trans hrows
  · rw [machineNearbyMatrixStep]
    cases hcurrentCode : machineNearbyMatrixCurrent state with
    | nil => exact False.elim (hc hcurrentCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineNearbyMatrixProcessEntry]
        simp only [MachineNearbyMatrixStateBound,
          machineNearbyMatrixSource_pack, machineNearbyMatrixRows_pack,
          machineNearbyMatrixCurrent_pack, machineNearbyMatrixAcc_pack,
          machineNearbyMatrixBound_pack]
        refine ⟨trivial, hsource, hrows, ?_, ?_, hbound⟩
        · exact (machinePairSecond_length_le
            (machineNearbyMatrixCurrent state)).trans hcurrent
        · rw [machineNearbyMatrixNextAcc, hbound]
          exact List.length_take_le _ _

theorem machineNearbyMatrixIterate_bound (word : List Bool) : ∀ k,
    MachineNearbyMatrixStateBound word
      ((machineNearbyMatrixStep)^[k] (machineNearbyMatrixInit word)) := by
  intro k
  induction k with
  | zero => exact machineNearbyMatrixInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineNearbyMatrixStep_bound ih

theorem machineNearbyMatrixIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineNearbyMatrixStep)^[iterations]
      (machineNearbyMatrixInit word)).length ≤
        (machineNearbyMatrixWidth word).length := by
  rcases machineNearbyMatrixIterate_bound word iterations with
    ⟨hdecomp, hsource, hrows, hcurrent, hacc, hbound⟩
  rw [hdecomp, hsource, hbound]
  simp only [machineNearbyMatrixPack, machineNearbyMatrixWidth, pair_length]
  omega

theorem machineNearbyMatrixFinalState_mem_FP :
    machineNearbyMatrixFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineNearbyMatrixStep_mem_FP
    machineNearbyMatrixInit_mem_FP id_mem_FP machineNearbyMatrixWidth_mem_FP
    machineNearbyMatrixIterate_length_le_width

theorem machineNearbyMatrixRawSumCode_mem_FP :
    machineNearbyMatrixRawSumCode ∈ Complexity.FP := by
  simpa only [machineNearbyMatrixRawSumCode] using!
    machineCompose_mem_FP machineNearbyMatrixFinalState_mem_FP
      machineNearbyMatrixAcc_mem_FP

/-! ## Semantic invariant and exactness before discharging the size bound -/

def rawNearbyListCost (tau : RawRat) (p : ℕ) (xs : List ℚ) : ℕ :=
  (xs.map fun q => rawRatWidth (rawNearbyCoordinateLower tau q p) + 1).sum

def rawNearbyRowsCost (tau : RawRat) (p : ℕ)
    (rows : List (List ℚ)) : ℕ :=
  (rows.map (rawNearbyListCost tau p)).sum

/-- Uniform raw-width budget for one coordinate whose canonical matrix entry,
matrix dimension, and requested precision are all controlled by a word of
length `L`.  The constants come directly from the normalized complement,
the `n + 400` schedule, and the fixed regularization constant. -/
def rawNearbyCoordinateInputWidthBudget (L : ℕ) : ℕ :=
  64 * ((L + 400) + 2 * (44 + 12 * L) + 4) ^ 2 *
      ((44 + 12 * L) + 2) +
    (L + 235) + L +
    64 * ((L + 400) + 2 * L + 4) ^ 2 * (L + 2) + 1

theorem rawCertificateRegularizationScale_width_le_optimizer_word
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    rawRatWidth (rawCertificateRegularizationScale n) ≤
      (rationalOptimizerOutputCode ⟨X, R, C⟩).length + 235 := by
  let word := rationalOptimizerOutputCode ⟨X, R, C⟩
  have hxi : rawRatWidth rawExplicitXi = 231 := by
    rw [rawExplicitXi, explicitXi, explicitDelta, explicitEta,
      explicitRowRatio]
    norm_num [rawRatOfRat, rawRatWidth]
    apply Nat.le_antisymm
    · apply max_le
      · norm_num
      · rw [Nat.size_le]
        norm_num
    · apply le_max_of_le_right
      have hsize : 230 < Nat.size
          1785851933491520000000000000000000000000000000000000000000000000000000 := by
        rw [Nat.lt_size]
        norm_num
      omega
  have hfour : rawRatWidth rawCertificateFour = 3 := by
    decide
  have hnraw := RawRat.width_ofNat_le n
  have hfourN := rawRatWidth_mul_le rawCertificateFour (RawRat.ofNat n)
  have htau := rawRatWidth_div_le rawExplicitXi
    (rawCertificateFourDimension n)
  have hnMatrix := matrix_dimension_le_code_length X
  have hmatrixWord :
      (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length ≤ word.length := by
    simpa only [word, rationalOptimizerOutputCode,
      machinePairFirst_pair] using! machinePairFirst_length_le word
  have hnWord : n ≤ word.length := hnMatrix.trans hmatrixWord
  simp only [rawCertificateRegularizationScale,
    rawCertificateFourDimension] at htau
  rw [hxi] at htau
  rw [hfour] at hfourN
  rw [rawCertificateRegularizationScale,
    rawCertificateFourDimension]
  dsimp only [word] at hnWord ⊢
  omega

theorem rawNearbyCoordinateLower_width_le_optimizer_word
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    {row : List ℚ} (hrow : row ∈ rationalMatrixRows X)
    {q : ℚ} (hq : q ∈ row) :
    rawRatWidth
        (rawNearbyCoordinateLower (rawCertificateRegularizationScale n) q
          (directedCertificatePrecision n)) ≤
      rawNearbyCoordinateInputWidthBudget
        (rationalOptimizerOutputCode ⟨X, R, C⟩).length := by
  let word := rationalOptimizerOutputCode ⟨X, R, C⟩
  let L := word.length
  have hrowsCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows X)).length ≤ L := by
    calc
      _ = (machineMatrixRowsWord
          (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)).length := by
        simpa using! congrArg List.length
          (machineMatrixRowsWord_encode X).symm
      _ ≤ (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length := by
        simpa only [machineMatrixRowsWord] using! machinePairSecond_length_le
          (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)
      _ ≤ word.length := by
        simpa only [word, rationalOptimizerOutputCode,
          machinePairFirst_pair] using! machinePairFirst_length_le word
      _ = L := rfl
  have hqCode := binaryListCode_element_length_le
    rationalEntryBinaryCode hq
  have hrowCode := binaryListCode_element_length_le
    (binaryListCode rationalEntryBinaryCode) hrow
  have hqWidth : rawRatWidth (rawRatOfRat q) ≤ L := by
    have hentryCode :
        (rawRatBinaryCode (rawRatOfRat q)).length ≤ L := by
      rw [rawRatBinaryCode_rawRatOfRat]
      exact hqCode.trans (hrowCode.trans hrowsCode)
    exact (rawRatWidth_le_binaryCode_length _).trans hentryCode
  have hnMatrix := matrix_dimension_le_code_length X
  have hmatrixWord :
      (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length ≤ L := by
    simpa only [L, word, rationalOptimizerOutputCode,
      machinePairFirst_pair] using! machinePairFirst_length_le word
  have hnWord : n ≤ L := hnMatrix.trans hmatrixWord
  have hp : directedCertificatePrecision n ≤ L + 400 := by
    simp only [directedCertificatePrecision]
    omega
  have hcompWidth0 := rawRatWidth_complement_le q
  have hcompWidth : rawRatWidth (rawRatOfRat (1 - q)) ≤ 44 + 12 * L := by
    omega
  have hcompLog := rawRatWidth_scheduledLogLower_of_bounds_le
    (1 - q) hp hcompWidth
  have hqLog := rawRatWidth_scheduledLogLower_of_bounds_le q hp hqWidth
  have htau := rawCertificateRegularizationScale_width_le_optimizer_word
    X R C
  have htx := rawRatWidth_mul_le
    (rawCertificateRegularizationScale n) (rawRatOfRat q)
  have hweighted := rawRatWidth_mul_le
    ((rawCertificateRegularizationScale n).mul (rawRatOfRat q))
    (rawScheduledLogLower q (directedCertificatePrecision n))
  have hadd := rawRatWidth_add_le
    (rawScheduledLogLower (1 - q) (directedCertificatePrecision n))
    (((rawCertificateRegularizationScale n).mul (rawRatOfRat q)).mul
      (rawScheduledLogLower q (directedCertificatePrecision n)))
  rw [rawNearbyCoordinateLower]
  simp only [rawNearbyCoordinateInputWidthBudget]
  dsimp only [L, word] at hqWidth hcompLog hqLog htx hweighted hadd
  exact hadd.trans (by omega)

theorem rawNearbyListCost_le_uniform {tau : RawRat} {p budget : ℕ} :
    ∀ xs : List ℚ,
    (∀ q ∈ xs,
      rawRatWidth (rawNearbyCoordinateLower tau q p) ≤ budget) →
    rawNearbyListCost tau p xs ≤ xs.length * (budget + 1) := by
  intro xs hwidth
  induction xs with
  | nil => simp [rawNearbyListCost]
  | cons q qs ih =>
      have hq := hwidth q (by simp)
      have hqs : ∀ r ∈ qs,
          rawRatWidth (rawNearbyCoordinateLower tau r p) ≤ budget := by
        intro r hr
        exact hwidth r (by simp [hr])
      have ih' := ih hqs
      simp only [rawNearbyListCost] at ih'
      simp only [rawNearbyListCost, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem rawNearbyRowsCost_le_uniform {tau : RawRat} {p budget : ℕ} :
    ∀ rows : List (List ℚ),
    (∀ row ∈ rows, ∀ q ∈ row,
      rawRatWidth (rawNearbyCoordinateLower tau q p) ≤ budget) →
    rawNearbyRowsCost tau p rows ≤
      (rows.map List.length).sum * (budget + 1) := by
  intro rows hwidth
  induction rows with
  | nil => simp [rawNearbyRowsCost]
  | cons row rows ih =>
      have hrow := rawNearbyListCost_le_uniform row (by
        intro q hq
        exact hwidth row (by simp) q hq)
      have hrows : ∀ tailRow ∈ rows, ∀ q ∈ tailRow,
          rawRatWidth (rawNearbyCoordinateLower tau q p) ≤ budget := by
        intro tailRow htail q hq
        exact hwidth tailRow (by simp [htail]) q hq
      have ih' := ih hrows
      simp only [rawNearbyRowsCost] at ih'
      simp only [rawNearbyRowsCost, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [Nat.add_mul]
      omega

theorem rawNearbyRowsCost_le_optimizer_word
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    rawNearbyRowsCost (rawCertificateRegularizationScale n)
        (directedCertificatePrecision n) (rationalMatrixRows X) ≤
      (rationalOptimizerOutputCode ⟨X, R, C⟩).length *
        (rawNearbyCoordinateInputWidthBudget
          (rationalOptimizerOutputCode ⟨X, R, C⟩).length + 1) := by
  let rows := rationalMatrixRows X
  let word := rationalOptimizerOutputCode ⟨X, R, C⟩
  let budget := rawNearbyCoordinateInputWidthBudget word.length
  have hcoordinate : ∀ row ∈ rows, ∀ q ∈ row,
      rawRatWidth
          (rawNearbyCoordinateLower (rawCertificateRegularizationScale n) q
            (directedCertificatePrecision n)) ≤ budget := by
    intro row hrow q hq
    simpa only [rows, word, budget] using!
      rawNearbyCoordinateLower_width_le_optimizer_word X R C hrow hq
  have hcost := rawNearbyRowsCost_le_uniform rows hcoordinate
  have hrowsCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machineMatrixRowsWord
          (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)).length := by
        simpa only [rows] using! congrArg List.length
          (machineMatrixRowsWord_encode X).symm
      _ ≤ (rationalMatrixBinaryEncoding.encode ⟨n, X⟩).length := by
        simpa only [machineMatrixRowsWord] using! machinePairSecond_length_le
          (rationalMatrixBinaryEncoding.encode ⟨n, X⟩)
      _ ≤ word.length := by
        simpa only [word, rationalOptimizerOutputCode,
          machinePairFirst_pair] using! machinePairFirst_length_le word
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsCode
  have hentries : (rows.map List.length).sum ≤ word.length := by
    have hentriesWork : ∀ rs : List (List ℚ),
        (rs.map List.length).sum ≤ matrixNonnegativeRowsWork rs := by
      intro rs
      induction rs with
      | nil => simp [matrixNonnegativeRowsWork]
      | cons row rs ih =>
          simp only [List.map_cons, List.sum_cons,
            matrixNonnegativeRowsWork]
          omega
    exact (hentriesWork rows).trans hwork
  have hmul := Nat.mul_le_mul_right (budget + 1) hentries
  exact hcost.trans (by simpa only [rows, word, budget] using! hmul)

theorem machineNearbyMatrixInputBound_length_dominates (word : List Bool) :
    4 + 3 * (1 + word.length *
      (rawNearbyCoordinateInputWidthBudget word.length + 1)) ≤
        (machineNearbyMatrixInputBound word).length := by
  simp only [rawNearbyCoordinateInputWidthBudget,
    machineNearbyMatrixInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  by_cases hsmall : word.length < 9
  · interval_cases word.length <;> norm_num
  · have h9 : 9 ≤ word.length := by omega
    have hsq : 81 ≤ word.length ^ 2 := by
      exact_mod_cast Nat.pow_le_pow_left h9 2
    have hcoef : 272148486 ≤ 3393120 * 81 := by norm_num
    have hcover :
        272148486 * word.length ^ 2 ≤ 3393120 * word.length ^ 4 := by
      calc
        272148486 * word.length ^ 2 ≤
            (3393120 * 81) * word.length ^ 2 :=
          Nat.mul_le_mul_right (word.length ^ 2) hcoef
        _ ≤ (3393120 * word.length ^ 2) * word.length ^ 2 := by
          exact Nat.mul_le_mul_right (word.length ^ 2)
            (Nat.mul_le_mul_left 3393120 hsq)
        _ = 3393120 * word.length ^ 4 := by ring
    ring_nf at hcover ⊢
    omega

def rawNearbyListSum (tau : RawRat) (p : ℕ) :
    RawRat → List ℚ → RawRat
  | acc, [] => acc
  | acc, q :: qs =>
      rawNearbyListSum tau p
        (acc.add (rawNearbyCoordinateLower tau q p)) qs

def rawNearbyRowsSum (tau : RawRat) (p : ℕ) :
    RawRat → List (List ℚ) → RawRat
  | acc, [] => acc
  | acc, row :: rows =>
      rawNearbyRowsSum tau p (rawNearbyListSum tau p acc row) rows

structure NearbyMatrixSemState where
  rows : List (List ℚ)
  current : List ℚ
  acc : RawRat

def nearbyMatrixSemStep (tau : RawRat) (p : ℕ)
    (s : NearbyMatrixSemState) : NearbyMatrixSemState :=
  match s.current with
  | q :: qs =>
      ⟨s.rows, qs, s.acc.add (rawNearbyCoordinateLower tau q p)⟩
  | [] =>
      match s.rows with
      | row :: rows => ⟨rows, row, s.acc⟩
      | [] => s

def nearbyMatrixSemCode (source bound : List Bool)
    (s : NearbyMatrixSemState) : List Bool :=
  machineNearbyMatrixPack source
    (binaryListCode (binaryListCode rationalEntryBinaryCode) s.rows)
    (binaryListCode rationalEntryBinaryCode s.current)
    (rawRatBinaryCode s.acc) bound

def NearbyMatrixSemInvariant (tau : RawRat) (p budget : ℕ)
    (s : NearbyMatrixSemState) : Prop :=
  rawRatWidth s.acc + rawNearbyListCost tau p s.current +
      rawNearbyRowsCost tau p s.rows ≤ budget

theorem nearbyMatrixSemStep_invariant {tau : RawRat} {p budget : ℕ}
    {s : NearbyMatrixSemState}
    (hs : NearbyMatrixSemInvariant tau p budget s) :
    NearbyMatrixSemInvariant tau p budget (nearbyMatrixSemStep tau p s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil => exact hs
      | cons row rows =>
          simp [NearbyMatrixSemInvariant, nearbyMatrixSemStep,
            rawNearbyRowsCost, rawNearbyListCost] at hs ⊢
          omega
  | cons q qs =>
      have hadd := rawRatWidth_add_le acc
        (rawNearbyCoordinateLower tau q p)
      simp only [NearbyMatrixSemInvariant, nearbyMatrixSemStep,
        rawNearbyListCost, List.map_cons, List.sum_cons] at hs ⊢
      omega

@[simp] theorem machineNearbyMatrixRowsWord_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineNearbyMatrixRowsWord
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows X) := by
  simp [machineNearbyMatrixRowsWord]

@[simp] theorem machineNearbyMatrixCoordinateRawCode_semCode
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rows : List (List ℚ)) (q : ℚ) (qs : List ℚ)
    (acc : RawRat) (bound : List Bool) :
    machineNearbyMatrixCoordinateRawCode
        (nearbyMatrixSemCode (rationalOptimizerOutputCode ⟨X, R, C⟩)
          bound ⟨rows, q :: qs, acc⟩) =
      rawRatBinaryCode
        (rawNearbyCoordinateLower
          (rawCertificateRegularizationScale n) q
          (directedCertificatePrecision n)) := by
  rw [machineNearbyMatrixCoordinateRawCode,
    machineNearbyMatrixCoordinateInput]
  simp only [nearbyMatrixSemCode, machineNearbyMatrixSource_pack,
    machineNearbyMatrixEntry, machineNearbyMatrixCurrent_pack,
    machineListHead_cons, machineCertificateLogPrecisionRuler_encode,
    machineCertificateRegularizationScaleRawCode_encode,
    machineNearbyCoordinateLowerRawCode_encode]

@[simp] theorem machineNearbyMatrixCoordinateRawCode_pack
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (rows : List (List ℚ)) (q : ℚ) (qs : List ℚ)
    (acc : RawRat) (bound : List Bool) :
    machineNearbyMatrixCoordinateRawCode
        (machineNearbyMatrixPack
          (rationalOptimizerOutputCode ⟨X, R, C⟩)
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
          (binaryListCode rationalEntryBinaryCode (q :: qs))
          (rawRatBinaryCode acc) bound) =
      rawRatBinaryCode
        (rawNearbyCoordinateLower
          (rawCertificateRegularizationScale n) q
          (directedCertificatePrecision n)) := by
  simpa only [nearbyMatrixSemCode] using!
    machineNearbyMatrixCoordinateRawCode_semCode X R C rows q qs acc bound

theorem machineNearbyMatrixStep_semantics
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (bound : List Bool) (s : NearbyMatrixSemState) (budget : ℕ)
    (hs : NearbyMatrixSemInvariant
      (rawCertificateRegularizationScale n)
      (directedCertificatePrecision n) budget s)
    (hlarge : 4 + 3 * budget ≤ bound.length) :
    machineNearbyMatrixStep
        (nearbyMatrixSemCode (rationalOptimizerOutputCode ⟨X, R, C⟩)
          bound s) =
      nearbyMatrixSemCode (rationalOptimizerOutputCode ⟨X, R, C⟩)
        bound (nearbyMatrixSemStep
          (rawCertificateRegularizationScale n)
          (directedCertificatePrecision n) s) := by
  rcases s with ⟨rows, current, acc⟩
  cases current with
  | nil =>
      cases rows with
      | nil =>
          simp [nearbyMatrixSemCode, nearbyMatrixSemStep,
            machineNearbyMatrixStep, machineNearbyMatrixAfterRow,
            binaryListCode]
      | cons row rows =>
          rw [nearbyMatrixSemCode, nearbyMatrixSemStep,
            machineNearbyMatrixStep]
          simp only [machineNearbyMatrixCurrent_pack, binaryListCode,
            machineIfEmpty_nil, machineNearbyMatrixAfterRow,
            machineNearbyMatrixRows_pack]
          have hpair : pair (binaryListCode rationalEntryBinaryCode row)
              (binaryListCode (binaryListCode rationalEntryBinaryCode) rows) ≠
                [] := by
            intro h
            have hlen := congrArg List.length h
            simp at hlen
          rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hpair]
          simp [machineNearbyMatrixLoadRow, nearbyMatrixSemCode,
            machineListHead, machineListTail]
  | cons q qs =>
      have hnext :
          rawRatWidth
              (acc.add (rawNearbyCoordinateLower
                (rawCertificateRegularizationScale n) q
                (directedCertificatePrecision n))) ≤ budget := by
        have hinv := nearbyMatrixSemStep_invariant hs
        have hinv' :
            rawRatWidth
                (acc.add (rawNearbyCoordinateLower
                  (rawCertificateRegularizationScale n) q
                  (directedCertificatePrecision n))) +
              rawNearbyListCost (rawCertificateRegularizationScale n)
                (directedCertificatePrecision n) qs +
              rawNearbyRowsCost (rawCertificateRegularizationScale n)
                (directedCertificatePrecision n) rows ≤ budget := by
          simpa only [NearbyMatrixSemInvariant, nearbyMatrixSemStep] using! hinv
        omega
      have hcode :
          (rawRatBinaryCode
            (acc.add (rawNearbyCoordinateLower
              (rawCertificateRegularizationScale n) q
              (directedCertificatePrecision n)))).length ≤ bound.length :=
        (rawRatBinaryCode_length_le_width _).trans
          ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnext) 4).trans
            hlarge)
      rw [nearbyMatrixSemCode, nearbyMatrixSemStep,
        machineNearbyMatrixStep]
      simp only [machineNearbyMatrixCurrent_pack]
      rw [machineIfEmpty_of_ne_nil_matrix _ _ _
        (binaryListCode_cons_ne_nil rationalEntryBinaryCode q qs)]
      simp only [machineNearbyMatrixProcessEntry,
        machineNearbyMatrixSource_pack, machineNearbyMatrixRows_pack,
        machineNearbyMatrixCurrent_pack, machineNearbyMatrixAcc_pack,
        machineNearbyMatrixBound_pack, machineListTail_cons,
        machineNearbyMatrixNextAcc, machineNearbyMatrixCandidate,
        machineNearbyMatrixCoordinateRawCode_pack]
      rw [machineRawRatAddCode_encode]
      rw [(List.take_eq_self_iff _).mpr hcode]
      rfl

theorem machineNearbyMatrixIterate_semantics
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (bound : List Bool) (s : NearbyMatrixSemState) (budget : ℕ)
    (hs : NearbyMatrixSemInvariant
      (rawCertificateRegularizationScale n)
      (directedCertificatePrecision n) budget s)
    (hlarge : 4 + 3 * budget ≤ bound.length) : ∀ k,
    (machineNearbyMatrixStep)^[k]
        (nearbyMatrixSemCode (rationalOptimizerOutputCode ⟨X, R, C⟩)
          bound s) =
      nearbyMatrixSemCode (rationalOptimizerOutputCode ⟨X, R, C⟩)
        bound
        ((nearbyMatrixSemStep (rawCertificateRegularizationScale n)
          (directedCertificatePrecision n))^[k] s) := by
  intro k
  have hinv : ∀ t : ℕ,
      NearbyMatrixSemInvariant (rawCertificateRegularizationScale n)
        (directedCertificatePrecision n) budget
        ((nearbyMatrixSemStep (rawCertificateRegularizationScale n)
          (directedCertificatePrecision n))^[t] s) := by
    intro t
    induction t with
    | zero => exact hs
    | succ t iht =>
        rw [Function.iterate_succ_apply']
        exact nearbyMatrixSemStep_invariant iht
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact machineNearbyMatrixStep_semantics X R C bound _ budget
        (hinv k) hlarge

theorem nearbyMatrixSem_processRow
    (tau : RawRat) (p : ℕ) (rows : List (List ℚ))
    (row : List ℚ) (acc : RawRat) :
    (nearbyMatrixSemStep tau p)^[row.length]
        ⟨rows, row, acc⟩ =
      ⟨rows, [], rawNearbyListSum tau p acc row⟩ := by
  induction row generalizing acc with
  | nil => rfl
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        nearbyMatrixSemStep, ih]
      rfl

theorem nearbyMatrixSem_processRows
    (tau : RawRat) (p : ℕ) (rows : List (List ℚ)) (acc : RawRat) :
    (nearbyMatrixSemStep tau p)^[matrixNonnegativeRowsWork rows]
        ⟨rows, [], acc⟩ =
      ⟨[], [], rawNearbyRowsSum tau p acc rows⟩ := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rows ih =>
      rw [matrixNonnegativeRowsWork, show 1 + row.length +
          matrixNonnegativeRowsWork rows =
          matrixNonnegativeRowsWork rows + row.length + 1 by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, nearbyMatrixSemStep,
        nearbyMatrixSem_processRow, ih, rawNearbyRowsSum]

theorem machineNearbyMatrix_done_iterate
    (extra : ℕ) (source : List Bool) (acc : RawRat) (bound : List Bool) :
    (machineNearbyMatrixStep)^[extra]
        (machineNearbyMatrixPack source [] [] (rawRatBinaryCode acc) bound) =
      machineNearbyMatrixPack source [] [] (rawRatBinaryCode acc) bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineNearbyMatrixStep, machineNearbyMatrixAfterRow]

theorem machineNearbyMatrixRawSumCode_encode_of_large
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (hlarge :
      4 + 3 * (1 + rawNearbyRowsCost
        (rawCertificateRegularizationScale n)
        (directedCertificatePrecision n) (rationalMatrixRows X)) ≤
      (machineNearbyMatrixInputBound
        (rationalOptimizerOutputCode ⟨X, R, C⟩)).length) :
    machineNearbyMatrixRawSumCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode
        (rawNearbyRowsSum (rawCertificateRegularizationScale n)
          (directedCertificatePrecision n) RawRat.zero
          (rationalMatrixRows X)) := by
  let rows := rationalMatrixRows X
  let word := rationalOptimizerOutputCode ⟨X, R, C⟩
  let tau := rawCertificateRegularizationScale n
  let p := directedCertificatePrecision n
  let s : NearbyMatrixSemState := ⟨rows, [], RawRat.zero⟩
  let budget := 1 + rawNearbyRowsCost tau p rows
  have hrowsLength :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machineNearbyMatrixRowsWord word).length := by
        simpa only [word, rows] using! congrArg List.length
          (machineNearbyMatrixRowsWord_encode X R C).symm
      _ ≤ word.length := by
        exact (machinePairSecond_length_le
          (machineOptimizerMatrixWord word)).trans
            (machinePairFirst_length_le word)
  have hinv : NearbyMatrixSemInvariant tau p budget s := by
    simp [NearbyMatrixSemInvariant, s, budget, rawNearbyListCost,
      rawRatWidth_zero]
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsLength
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  have hinit : machineNearbyMatrixInit word =
      nearbyMatrixSemCode word (machineNearbyMatrixInputBound word) s := by
    simp [machineNearbyMatrixInit, nearbyMatrixSemCode, s, word, rows,
      binaryListCode, machineNearbyMatrixRowsWord]
  have hlarge' :
      4 + 3 * budget ≤ (machineNearbyMatrixInputBound word).length := by
    simpa only [budget, tau, p, rows, word] using! hlarge
  rw [machineNearbyMatrixRawSumCode, machineNearbyMatrixFinalState,
    hsplit, Function.iterate_add_apply, hinit,
    machineNearbyMatrixIterate_semantics X R C
      (machineNearbyMatrixInputBound word) s budget hinv hlarge',
    nearbyMatrixSem_processRows]
  simp only [nearbyMatrixSemCode, binaryListCode]
  rw [machineNearbyMatrix_done_iterate]
  simp [rows]

@[simp] theorem machineNearbyMatrixRawSumCode_encode
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineNearbyMatrixRawSumCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode
        (rawNearbyRowsSum (rawCertificateRegularizationScale n)
          (directedCertificatePrecision n) RawRat.zero
          (rationalMatrixRows X)) := by
  apply machineNearbyMatrixRawSumCode_encode_of_large X R C
  let word := rationalOptimizerOutputCode ⟨X, R, C⟩
  have hcost := rawNearbyRowsCost_le_optimizer_word X R C
  have hruler := machineNearbyMatrixInputBound_length_dominates word
  dsimp only [word] at hruler
  omega

theorem rawNearbyListSum_value (tau : RawRat) (p : ℕ)
    (acc : RawRat) : ∀ xs : List ℚ,
    (rawNearbyListSum tau p acc xs).value =
      acc.value + (xs.map (directedNearbyCoordinateLower tau.value · p)).sum := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawNearbyListSum]
  | cons q qs ih =>
      rw [rawNearbyListSum, ih]
      simp [rawNearbyCoordinateLower_value, add_assoc]

theorem rawNearbyRowsSum_value (tau : RawRat) (p : ℕ)
    (acc : RawRat) : ∀ rows : List (List ℚ),
    (rawNearbyRowsSum tau p acc rows).value =
      acc.value +
        (rows.map fun row =>
          (row.map (directedNearbyCoordinateLower tau.value · p)).sum).sum := by
  intro rows
  induction rows generalizing acc with
  | nil => simp [rawNearbyRowsSum]
  | cons row rows ih =>
      rw [rawNearbyRowsSum, ih, rawNearbyListSum_value]
      simp [add_assoc]

theorem rationalMatrixRows_nearby_sum {n : ℕ}
    (tau : ℚ) (X : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) :
    ((rationalMatrixRows X).map fun row =>
        (row.map (directedNearbyCoordinateLower tau · p)).sum).sum =
      ∑ i, ∑ j, directedNearbyCoordinateLower tau (X i j) p := by
  simp [rationalMatrixRows, List.sum_ofFn]

theorem rawNearbyRowsSum_certificate_value {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    (rawNearbyRowsSum (rawCertificateRegularizationScale n)
      (directedCertificatePrecision n) RawRat.zero
      (rationalMatrixRows X)).value =
        ∑ i, ∑ j, directedNearbyCoordinateLower
          (explicitRegularizationScale n) (X i j)
          (directedCertificatePrecision n) := by
  rw [rawNearbyRowsSum_value, rawCertificateRegularizationScale_value,
    rationalMatrixRows_nearby_sum]
  simp

end BeyondBethe
