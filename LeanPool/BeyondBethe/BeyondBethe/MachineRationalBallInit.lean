/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidEncoding
import LeanPool.BeyondBethe.BeyondBethe.MachineRepeatPair
import LeanPool.BeyondBethe.BeyondBethe.MachineNestedMatrixMemory
import LeanPool.BeyondBethe.BeyondBethe.MachineLengthBits

/-! # Machine Rational Ball Init -/

namespace BeyondBethe

open Complexity

/-!
# Finite-word construction of rational ball states

This module begins the concrete state constructor used by every feasibility
call.  It first builds the zero center and all-zero square basis from a unary
dimension ruler.  The following section will replace the diagonal entries by
the encoded radius and package the result as a complete ellipsoid state.
-/

def machineRationalZeroEntry : List Bool :=
  rationalEntryBinaryCode 0

/-- Input: a unary dimension ruler. -/
def machineRationalZeroVectorCode (ruler : List Bool) : List Bool :=
  machineRepeatPairCode
    (pair ruler (pair machineRationalZeroEntry []))

/-- Input: a unary dimension ruler. -/
def machineRationalZeroMatrixRowsCode (ruler : List Bool) : List Bool :=
  let row := machineRationalZeroVectorCode ruler
  machineRepeatPairCode (pair ruler (pair row []))

theorem machineRationalZeroVectorCode_mem_FP :
    machineRationalZeroVectorCode ∈ FP := by
  have hpayload := machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP machineRationalZeroEntry)
      (machineConst_mem_FP []))
  simpa only [machineRationalZeroVectorCode] using
    machineCompose_mem_FP hpayload machineRepeatPairCode_mem_FP

theorem machineRationalZeroMatrixRowsCode_mem_FP :
    machineRationalZeroMatrixRowsCode ∈ FP := by
  have hpayload := machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineRationalZeroVectorCode_mem_FP
      (machineConst_mem_FP []))
  simpa only [machineRationalZeroMatrixRowsCode] using
    machineCompose_mem_FP hpayload machineRepeatPairCode_mem_FP

@[simp] theorem machineRationalZeroVectorCode_encode (d : ℕ) :
    machineRationalZeroVectorCode (List.replicate d true) =
      rationalFiniteVectorCode (fun _ : Fin d ↦ (0 : ℚ)) := by
  rw [machineRationalZeroVectorCode]
  change machineRepeatPairCode
      (machineRepeatPairCanonicalInput d machineRationalZeroEntry []) = _
  rw [machineRepeatPairCode_encode]
  change repeatPairCode d (rationalEntryBinaryCode 0)
      (binaryListCode rationalEntryBinaryCode []) = _
  rw [repeatPairCode_binaryListCode]
  simp [rationalFiniteVectorCode]

theorem rationalMatrixRows_zero (d : ℕ) :
    rationalMatrixRows (0 : Matrix (Fin d) (Fin d) ℚ) =
      List.replicate d (List.replicate d 0) := by
  simp [rationalMatrixRows]

@[simp] theorem machineRationalZeroMatrixRowsCode_encode (d : ℕ) :
    machineRationalZeroMatrixRowsCode (List.replicate d true) =
      rationalSquareMatrixRowsCode
        (0 : Matrix (Fin d) (Fin d) ℚ) := by
  rw [machineRationalZeroMatrixRowsCode,
    machineRationalZeroVectorCode_encode]
  change machineRepeatPairCode
    (machineRepeatPairCanonicalInput d
      (rationalFiniteVectorCode (fun _ : Fin d ↦ (0 : ℚ))) []) = _
  rw [machineRepeatPairCode_encode]
  change repeatPairCode d
      (binaryListCode rationalEntryBinaryCode
        (List.ofFn (fun _ : Fin d ↦ (0 : ℚ))))
      (binaryListCode (binaryListCode rationalEntryBinaryCode) []) = _
  rw [repeatPairCode_binaryListCode]
  rw [rationalSquareMatrixRowsCode, rationalMatrixRows_zero]
  simp

/-! ## Diagonal prefixes -/

/-- The first `k` diagonal entries have been replaced by `R`; all other
entries are zero. -/
def rationalDiagonalPrefixMatrix (d k : ℕ) (R : ℚ) :
    Matrix (Fin d) (Fin d) ℚ :=
  fun i j ↦ if i = j ∧ i.1 < k then R else 0

@[simp] theorem rationalDiagonalPrefixMatrix_zero
    (d : ℕ) (R : ℚ) :
    rationalDiagonalPrefixMatrix d 0 R = 0 := by
  ext i j
  simp [rationalDiagonalPrefixMatrix]

theorem rationalDiagonalPrefixMatrix_all
    (d : ℕ) (R : ℚ) :
    rationalDiagonalPrefixMatrix d d R =
      (rationalBallEllipsoid d 0 R).basis := by
  ext i j
  simp [rationalDiagonalPrefixMatrix, rationalBallEllipsoid]

theorem rationalMatrixRows_diagonalPrefix_set
    {d k : ℕ} (R : ℚ) (hk : k < d) :
    let rows := rationalMatrixRows (rationalDiagonalPrefixMatrix d k R)
    rows.set k
        ((rows[k]'(by simpa [rows, rationalMatrixRows] using hk)).set k R) =
      rationalMatrixRows (rationalDiagonalPrefixMatrix d (k + 1) R) := by
  dsimp only
  apply List.ext_getElem
  · simp [rationalMatrixRows]
  · intro i hiLeft hiRight
    have hi : i < d := by
      simpa [rationalMatrixRows] using hiRight
    by_cases hik : i = k
    · subst i
      simp only [List.getElem_set, ↓reduceIte]
      apply List.ext_getElem
      · simp [rationalMatrixRows]
      · intro j hjLeft hjRight
        have hj : j < d := by
          simpa [rationalMatrixRows] using hjRight
        by_cases hjk : j = k
        · subst j
          simp [rationalMatrixRows, rationalDiagonalPrefixMatrix]
        · rw [List.getElem_set_of_ne (Ne.symm hjk)]
          simp [rationalMatrixRows, rationalDiagonalPrefixMatrix,
            Ne.symm hjk]
    · rw [List.getElem_set_of_ne (Ne.symm hik)]
      simp only [rationalMatrixRows, List.getElem_ofFn]
      apply List.ext_getElem
      · simp
      · intro j hjLeft hjRight
        have hj : j < d := by simpa using hjRight
        simp only [List.getElem_ofFn]
        by_cases hij : i = j
        · subst j
          simp only [rationalDiagonalPrefixMatrix, Nat.lt_succ_iff]
          by_cases hlt : i < k
          · have hnki : ¬k < i := by omega
            simp [hlt, hnki]
          · have hgt : k < i := by omega
            simp [hlt, Nat.not_le.mpr hgt]
        · simp [rationalDiagonalPrefixMatrix, hij]

/-! ## Diagonal-basis machine -/

def machineDiagonalBasisRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDiagonalBasisRadiusEntry (word : List Bool) : List Bool :=
  machinePairSecond word

/-- A quartic envelope for the nested matrix under diagonal updates. -/
def machineDiagonalBasisBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth word)

def machineDiagonalBasisPack
    (index matrix radius bound : List Bool) : List Bool :=
  pair index (pair matrix (pair radius bound))

def machineDiagonalBasisIndex (state : List Bool) : List Bool :=
  machinePairFirst state

def machineDiagonalBasisMatrix (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineDiagonalBasisRadius (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineDiagonalBasisStateBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineDiagonalBasisNextIndexCandidate
    (state : List Bool) : List Bool :=
  true :: machineDiagonalBasisIndex state

def machineDiagonalBasisNextIndex (state : List Bool) : List Bool :=
  (machineDiagonalBasisNextIndexCandidate state).take
    (machineDiagonalBasisStateBound state).length

def machineDiagonalBasisMatrixCandidate (state : List Bool) : List Bool :=
  machineNestedMatrixUpdateAtUnary
    (pair (machineDiagonalBasisIndex state)
      (pair (machineDiagonalBasisIndex state)
        (pair (machineDiagonalBasisRadius state)
          (machineDiagonalBasisMatrix state))))

def machineDiagonalBasisNextMatrix (state : List Bool) : List Bool :=
  (machineDiagonalBasisMatrixCandidate state).take
    (machineDiagonalBasisStateBound state).length

def machineDiagonalBasisStep (state : List Bool) : List Bool :=
  machineDiagonalBasisPack (machineDiagonalBasisNextIndex state)
    (machineDiagonalBasisNextMatrix state)
    (machineDiagonalBasisRadius state)
    (machineDiagonalBasisStateBound state)

def machineDiagonalBasisInitialMatrix (word : List Bool) : List Bool :=
  (machineRationalZeroMatrixRowsCode (machineDiagonalBasisRuler word)).take
    (machineDiagonalBasisBound word).length

def machineDiagonalBasisInit (word : List Bool) : List Bool :=
  machineDiagonalBasisPack [] (machineDiagonalBasisInitialMatrix word)
    (machineDiagonalBasisRadiusEntry word)
    (machineDiagonalBasisBound word)

def machineDiagonalBasisWidth (word : List Bool) : List Bool :=
  machineDiagonalBasisPack (machineDiagonalBasisBound word)
    (machineDiagonalBasisBound word) (machineDiagonalBasisBound word)
    (machineDiagonalBasisBound word)

def machineDiagonalBasisFinalState (word : List Bool) : List Bool :=
  (machineDiagonalBasisStep)^[(machineDiagonalBasisRuler word).length]
    (machineDiagonalBasisInit word)

def machineDiagonalBasisRowsCode (word : List Bool) : List Bool :=
  machineDiagonalBasisMatrix (machineDiagonalBasisFinalState word)

/-! ### Polynomial-time closure -/

theorem machineDiagonalBasisRuler_mem_FP :
    machineDiagonalBasisRuler ∈ FP := machinePairFirst_mem_FP

theorem machineDiagonalBasisRadiusEntry_mem_FP :
    machineDiagonalBasisRadiusEntry ∈ FP := machinePairSecond_mem_FP

theorem machineDiagonalBasisBound_mem_FP :
    machineDiagonalBasisBound ∈ FP := by
  simpa only [machineDiagonalBasisBound] using
    machineCompose_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineDiagonalBasisIndex_mem_FP :
    machineDiagonalBasisIndex ∈ FP := machinePairFirst_mem_FP

theorem machineDiagonalBasisMatrix_mem_FP :
    machineDiagonalBasisMatrix ∈ FP := by
  simpa only [machineDiagonalBasisMatrix] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineDiagonalBasisRadius_mem_FP :
    machineDiagonalBasisRadius ∈ FP := by
  have hsecondTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineDiagonalBasisRadius] using
    machineCompose_mem_FP hsecondTwo machinePairFirst_mem_FP

theorem machineDiagonalBasisStateBound_mem_FP :
    machineDiagonalBasisStateBound ∈ FP := by
  have hsecondTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineDiagonalBasisStateBound] using
    machineCompose_mem_FP hsecondTwo machinePairSecond_mem_FP

theorem machineDiagonalBasisNextIndexCandidate_mem_FP :
    machineDiagonalBasisNextIndexCandidate ∈ FP := by
  simpa only [machineDiagonalBasisNextIndexCandidate] using
    machineAppend_mem_FP (machineConst_mem_FP [true])
      machineDiagonalBasisIndex_mem_FP

theorem machineDiagonalBasisNextIndex_mem_FP :
    machineDiagonalBasisNextIndex ∈ FP := by
  simpa only [machineDiagonalBasisNextIndex] using
    machineTake_mem_FP machineDiagonalBasisStateBound_mem_FP
      machineDiagonalBasisNextIndexCandidate_mem_FP

theorem machineDiagonalBasisMatrixCandidate_mem_FP :
    machineDiagonalBasisMatrixCandidate ∈ FP := by
  have hpayload := machinePair_mem_FP machineDiagonalBasisIndex_mem_FP
    (machinePair_mem_FP machineDiagonalBasisIndex_mem_FP
      (machinePair_mem_FP machineDiagonalBasisRadius_mem_FP
        machineDiagonalBasisMatrix_mem_FP))
  simpa only [machineDiagonalBasisMatrixCandidate] using
    machineCompose_mem_FP hpayload machineNestedMatrixUpdateAtUnary_mem_FP

theorem machineDiagonalBasisNextMatrix_mem_FP :
    machineDiagonalBasisNextMatrix ∈ FP := by
  simpa only [machineDiagonalBasisNextMatrix] using
    machineTake_mem_FP machineDiagonalBasisStateBound_mem_FP
      machineDiagonalBasisMatrixCandidate_mem_FP

theorem machineDiagonalBasisStep_mem_FP : machineDiagonalBasisStep ∈ FP :=
  machinePair_mem_FP machineDiagonalBasisNextIndex_mem_FP
    (machinePair_mem_FP machineDiagonalBasisNextMatrix_mem_FP
      (machinePair_mem_FP machineDiagonalBasisRadius_mem_FP
        machineDiagonalBasisStateBound_mem_FP))

theorem machineDiagonalBasisInitialMatrix_mem_FP :
    machineDiagonalBasisInitialMatrix ∈ FP := by
  have hzero := machineCompose_mem_FP machineDiagonalBasisRuler_mem_FP
    machineRationalZeroMatrixRowsCode_mem_FP
  simpa only [machineDiagonalBasisInitialMatrix] using
    machineTake_mem_FP machineDiagonalBasisBound_mem_FP hzero

theorem machineDiagonalBasisInit_mem_FP : machineDiagonalBasisInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP machineDiagonalBasisInitialMatrix_mem_FP
      (machinePair_mem_FP machineDiagonalBasisRadiusEntry_mem_FP
        machineDiagonalBasisBound_mem_FP))

theorem machineDiagonalBasisWidth_mem_FP : machineDiagonalBasisWidth ∈ FP :=
  machinePair_mem_FP machineDiagonalBasisBound_mem_FP
    (machinePair_mem_FP machineDiagonalBasisBound_mem_FP
      (machinePair_mem_FP machineDiagonalBasisBound_mem_FP
        machineDiagonalBasisBound_mem_FP))

@[simp] theorem machineDiagonalBasisIndex_pack (a b c e) :
    machineDiagonalBasisIndex (machineDiagonalBasisPack a b c e) = a := by
  simp [machineDiagonalBasisIndex, machineDiagonalBasisPack]

@[simp] theorem machineDiagonalBasisMatrix_pack (a b c e) :
    machineDiagonalBasisMatrix (machineDiagonalBasisPack a b c e) = b := by
  simp [machineDiagonalBasisMatrix, machineDiagonalBasisPack]

@[simp] theorem machineDiagonalBasisRadius_pack (a b c e) :
    machineDiagonalBasisRadius (machineDiagonalBasisPack a b c e) = c := by
  simp [machineDiagonalBasisRadius, machineDiagonalBasisPack]

@[simp] theorem machineDiagonalBasisStateBound_pack (a b c e) :
    machineDiagonalBasisStateBound (machineDiagonalBasisPack a b c e) = e := by
  simp [machineDiagonalBasisStateBound, machineDiagonalBasisPack]

def MachineDiagonalBasisStateBound (word state : List Bool) : Prop :=
  let B := (machineDiagonalBasisBound word).length
  state = machineDiagonalBasisPack
      (machineDiagonalBasisIndex state)
      (machineDiagonalBasisMatrix state)
      (machineDiagonalBasisRadius state)
      (machineDiagonalBasisStateBound state) ∧
    (machineDiagonalBasisIndex state).length ≤ B ∧
    (machineDiagonalBasisMatrix state).length ≤ B ∧
    (machineDiagonalBasisRadius state).length ≤ B ∧
    (machineDiagonalBasisStateBound state).length ≤ B

theorem machineDiagonalBasis_word_length_le_bound (word : List Bool) :
    word.length ≤ (machineDiagonalBasisBound word).length := by
  simp only [machineDiagonalBasisBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

theorem machineDiagonalBasisInit_bound (word : List Bool) :
    MachineDiagonalBasisStateBound word (machineDiagonalBasisInit word) := by
  simp only [MachineDiagonalBasisStateBound, machineDiagonalBasisInit,
    machineDiagonalBasisIndex_pack, machineDiagonalBasisMatrix_pack,
    machineDiagonalBasisRadius_pack, machineDiagonalBasisStateBound_pack]
  refine ⟨trivial, by simp, ?_, ?_, le_rfl⟩
  · exact (List.length_take_le _ _).trans le_rfl
  · exact (machinePairSecond_length_le word).trans
      (machineDiagonalBasis_word_length_le_bound word)

theorem machineDiagonalBasisStep_bound {word state : List Bool}
    (hstate : MachineDiagonalBasisStateBound word state) :
    MachineDiagonalBasisStateBound word (machineDiagonalBasisStep state) := by
  dsimp only [MachineDiagonalBasisStateBound] at hstate ⊢
  rcases hstate with ⟨_, _hindex, _hmatrix, hradius, hbound⟩
  simp only [machineDiagonalBasisStep, machineDiagonalBasisIndex_pack,
    machineDiagonalBasisMatrix_pack, machineDiagonalBasisRadius_pack,
    machineDiagonalBasisStateBound_pack]
  refine ⟨trivial, ?_, ?_, hradius, hbound⟩
  · exact (List.length_take_le _ _).trans hbound
  · exact (List.length_take_le _ _).trans hbound

theorem machineDiagonalBasisIterate_bound (word : List Bool) : ∀ k,
    MachineDiagonalBasisStateBound word
      ((machineDiagonalBasisStep)^[k] (machineDiagonalBasisInit word)) := by
  intro k
  induction k with
  | zero => exact machineDiagonalBasisInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineDiagonalBasisStep_bound ih

theorem machineDiagonalBasisIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineDiagonalBasisRuler word).length) :
    ((machineDiagonalBasisStep)^[iterations]
      (machineDiagonalBasisInit word)).length ≤
        (machineDiagonalBasisWidth word).length := by
  rcases machineDiagonalBasisIterate_bound word iterations with
    ⟨hdecomp, hindex, hmatrix, hradius, hbound⟩
  rw [hdecomp]
  simp only [machineDiagonalBasisPack, machineDiagonalBasisWidth, pair_length]
  omega

theorem machineDiagonalBasisFinalState_mem_FP :
    machineDiagonalBasisFinalState ∈ FP :=
  Cobham.iterate_mem_FP machineDiagonalBasisStep_mem_FP
    machineDiagonalBasisInit_mem_FP machineDiagonalBasisRuler_mem_FP
    machineDiagonalBasisWidth_mem_FP
    machineDiagonalBasisIterate_length_le_width

theorem machineDiagonalBasisRowsCode_mem_FP :
    machineDiagonalBasisRowsCode ∈ FP := by
  simpa only [machineDiagonalBasisRowsCode] using
    machineCompose_mem_FP machineDiagonalBasisFinalState_mem_FP
      machineDiagonalBasisMatrix_mem_FP

/-! ### Exact canonical semantics -/

def machineDiagonalBasisCanonicalInput (d : ℕ) (R : ℚ) : List Bool :=
  pair (List.replicate d true) (rationalEntryBinaryCode R)

def machineDiagonalBasisCanonicalState
    (d : ℕ) (R : ℚ) (k : ℕ) : List Bool :=
  let word := machineDiagonalBasisCanonicalInput d R
  machineDiagonalBasisPack (List.replicate k true)
    (rationalSquareMatrixRowsCode (rationalDiagonalPrefixMatrix d k R))
    (rationalEntryBinaryCode R) (machineDiagonalBasisBound word)

theorem rationalSquareMatrixRowsCode_diagonalPrefix_length_le
    (d k : ℕ) (R : ℚ) :
    (rationalSquareMatrixRowsCode
      (rationalDiagonalPrefixMatrix d k R)).length ≤
      d * (2 * (d *
        (2 * (machineRationalZeroEntry.length +
          (rationalEntryBinaryCode R).length) + 2)) + 2) := by
  let M := machineRationalZeroEntry.length +
    (rationalEntryBinaryCode R).length
  have hentry : ∀ i j : Fin d,
      (rationalEntryBinaryCode
        (rationalDiagonalPrefixMatrix d k R i j)).length ≤ M := by
    intro i j
    simp only [rationalDiagonalPrefixMatrix]
    split
    · omega
    · change machineRationalZeroEntry.length ≤ M
      omega
  rw [rationalSquareMatrixRowsCode, binaryListCode_length_eq_sum]
  simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  calc
    (∑ i : Fin d,
        (2 * (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalDiagonalPrefixMatrix d k R i j)).length +
          2)) ≤
      ∑ _i : Fin d, (2 * (d * (2 * M + 2)) + 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        rw [binaryListCode_length_eq_sum]
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
        calc
          (∑ j : Fin d,
              (2 * (rationalEntryBinaryCode
                (rationalDiagonalPrefixMatrix d k R i j)).length + 2)) ≤
            ∑ _j : Fin d, (2 * M + 2) := by
              apply Finset.sum_le_sum
              intro j _
              have he := hentry i j
              omega
          _ = d * (2 * M + 2) := by simp [mul_comm]
    _ = d * (2 * (d * (2 * M + 2)) + 2) := by simp [mul_comm]

theorem machineDiagonalBasis_prefix_fits
    (d k : ℕ) (R : ℚ) :
    (rationalSquareMatrixRowsCode
      (rationalDiagonalPrefixMatrix d k R)).length ≤
      (machineDiagonalBasisBound
        (machineDiagonalBasisCanonicalInput d R)).length := by
  let W := (machineDiagonalBasisCanonicalInput d R).length
  let Z := machineRationalZeroEntry.length
  let L := (rationalEntryBinaryCode R).length
  have hZ : Z = 5 := by
    decide
  have hW : W = 2 * d + 2 + L := by
    simp [W, L, machineDiagonalBasisCanonicalInput]
  have hL : 4 ≤ L := by
    dsimp only [L, rationalEntryBinaryCode]
    cases R.num <;> simp [integerBinaryCode] <;> omega
  have hdW : d ≤ W := by omega
  have hLW : L ≤ W := by omega
  have hZW : Z ≤ W := by omega
  have hM : Z + L ≤ 2 * W := by omega
  have hinner : d * (2 * (Z + L) + 2) ≤ 6 * W ^ 2 := by
    have hfactor : 2 * (Z + L) + 2 ≤ 6 * W := by
      have hWpos : 1 ≤ W := by omega
      omega
    have hmul := Nat.mul_le_mul hdW hfactor
    nlinarith
  have hrow : 2 * (d * (2 * (Z + L) + 2)) + 2 ≤
      14 * W ^ 2 := by
    have hWpos : 1 ≤ W := by omega
    nlinarith
  have hcode : d * (2 * (d * (2 * (Z + L) + 2)) + 2) ≤
      14 * W ^ 3 := by
    have hmul := Nat.mul_le_mul hdW hrow
    nlinarith
  have hshift : W ≤ 16 + W := by omega
  have hpow3 : W ^ 3 ≤ (16 + W) ^ 3 :=
    Nat.pow_le_pow_left hshift 3
  have h14 : 14 ≤ 16 + W := by omega
  have hcubic : 14 * W ^ 3 ≤ (16 + W) ^ 4 := by
    calc
      14 * W ^ 3 ≤ (16 + W) * (16 + W) ^ 3 :=
        Nat.mul_le_mul h14 hpow3
      _ = (16 + W) ^ 4 := by ring
  have hbase : (16 + W) ^ 2 ≤ 16 + (16 + W) ^ 2 := by omega
  have hquartic : (16 + W) ^ 4 ≤
      (16 + (16 + W) ^ 2) ^ 2 := by
    rw [show (16 + W) ^ 4 = ((16 + W) ^ 2) ^ 2 by ring]
    exact Nat.pow_le_pow_left hbase 2
  have hpref := rationalSquareMatrixRowsCode_diagonalPrefix_length_le
    d k R
  dsimp only [Z, L] at hpref hcode
  calc
    (rationalSquareMatrixRowsCode
        (rationalDiagonalPrefixMatrix d k R)).length ≤
      d * (2 * (d *
        (2 * (machineRationalZeroEntry.length +
          (rationalEntryBinaryCode R).length) + 2)) + 2) := hpref
    _ ≤ 14 * W ^ 3 := hcode
    _ ≤ (16 + W) ^ 4 := hcubic
    _ ≤ (16 + (16 + W) ^ 2) ^ 2 := hquartic
    _ = (machineDiagonalBasisBound
        (machineDiagonalBasisCanonicalInput d R)).length := by
      simp only [machineDiagonalBasisBound, machineBinaryMulWidth,
        List.length_replicate, List.length_append]
      rw [show (machineDiagonalBasisCanonicalInput d R).length = W by rfl]
      ring

theorem machineDiagonalBasisInit_semantics (d : ℕ) (R : ℚ) :
    machineDiagonalBasisInit (machineDiagonalBasisCanonicalInput d R) =
      machineDiagonalBasisCanonicalState d R 0 := by
  have hfit := machineDiagonalBasis_prefix_fits d 0 R
  have hzero : rationalSquareMatrixRowsCode
      (rationalDiagonalPrefixMatrix d 0 R) =
      rationalSquareMatrixRowsCode (0 : Matrix (Fin d) (Fin d) ℚ) := by
    rw [rationalDiagonalPrefixMatrix_zero]
  have htake :
      (machineRationalZeroMatrixRowsCode (List.replicate d true)).take
          (machineDiagonalBasisBound
            (machineDiagonalBasisCanonicalInput d R)).length =
        rationalSquareMatrixRowsCode
          (rationalDiagonalPrefixMatrix d 0 R) := by
    rw [machineRationalZeroMatrixRowsCode_encode, ← hzero]
    exact List.take_of_length_le hfit
  simp only [machineDiagonalBasisInit, machineDiagonalBasisCanonicalInput,
    machineDiagonalBasisCanonicalState, machineDiagonalBasisRuler,
    machineDiagonalBasisRadiusEntry, machinePairFirst_pair,
    machinePairSecond_pair, machineDiagonalBasisInitialMatrix]
  have htake' := htake
  simp only [machineDiagonalBasisCanonicalInput] at htake'
  rw [htake']
  simp

theorem machineDiagonalBasisStep_semantics
    (d k : ℕ) (R : ℚ) (hk : k < d) :
    machineDiagonalBasisStep
        (machineDiagonalBasisCanonicalState d R k) =
      machineDiagonalBasisCanonicalState d R (k + 1) := by
  let M := rationalMatrixRows (rationalDiagonalPrefixMatrix d k R)
  have hrow : k < M.length := by simp [M, rationalMatrixRows, hk]
  have hcol : k < M[k].length := by simp [M, rationalMatrixRows, hk]
  have hupdate := machineNestedMatrixUpdateAtUnary_encode
    rationalEntryBinaryCode M k k R hrow hcol
  rw [rationalMatrixRows_diagonalPrefix_set R hk] at hupdate
  have hmatrixFit := machineDiagonalBasis_prefix_fits d (k + 1) R
  have hmatrixTake :
      (machineDiagonalBasisMatrixCandidate
        (machineDiagonalBasisCanonicalState d R k)).take
          (machineDiagonalBasisBound
            (machineDiagonalBasisCanonicalInput d R)).length =
        rationalSquareMatrixRowsCode
          (rationalDiagonalPrefixMatrix d (k + 1) R) := by
    rw [machineDiagonalBasisMatrixCandidate,
      machineDiagonalBasisCanonicalState,
      machineDiagonalBasisIndex_pack, machineDiagonalBasisMatrix_pack,
      machineDiagonalBasisRadius_pack]
    simpa only [rationalSquareMatrixRowsCode] using
      congrArg (fun word ↦ word.take
        (machineDiagonalBasisBound
          (machineDiagonalBasisCanonicalInput d R)).length) hupdate |>.trans
        (List.take_of_length_le hmatrixFit)
  have hindexFit : k + 1 ≤
      (machineDiagonalBasisBound
        (machineDiagonalBasisCanonicalInput d R)).length := by
    have hword := machineDiagonalBasis_word_length_le_bound
      (machineDiagonalBasisCanonicalInput d R)
    have hdim : d ≤ (machineDiagonalBasisCanonicalInput d R).length := by
      simp only [machineDiagonalBasisCanonicalInput, pair_length,
        List.length_replicate]
      omega
    exact (show k + 1 ≤ d by omega).trans (hdim.trans hword)
  have hindexTake :
      (true :: List.replicate k true).take
          (machineDiagonalBasisBound
            (machineDiagonalBasisCanonicalInput d R)).length =
        List.replicate (k + 1) true := by
    have hrep : List.replicate (k + 1) true =
        true :: List.replicate k true := by
      rw [List.replicate_succ]
    rw [← hrep]
    exact List.take_of_length_le (by simpa using hindexFit)
  simp only [machineDiagonalBasisStep, machineDiagonalBasisCanonicalState,
    machineDiagonalBasisNextIndex, machineDiagonalBasisNextIndexCandidate,
    machineDiagonalBasisIndex_pack, machineDiagonalBasisNextMatrix,
    machineDiagonalBasisStateBound_pack, machineDiagonalBasisRadius_pack]
  rw [hindexTake]
  have hmatrixTake' := hmatrixTake
  simp only [machineDiagonalBasisCanonicalState] at hmatrixTake'
  rw [hmatrixTake']

theorem machineDiagonalBasisIterate_semantics
    (d : ℕ) (R : ℚ) : ∀ k ≤ d,
    (machineDiagonalBasisStep)^[k]
        (machineDiagonalBasisInit
          (machineDiagonalBasisCanonicalInput d R)) =
      machineDiagonalBasisCanonicalState d R k := by
  intro k hk
  induction k with
  | zero => exact machineDiagonalBasisInit_semantics d R
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineDiagonalBasisStep_semantics d k R (by omega)

@[simp] theorem machineDiagonalBasisRowsCode_encode (d : ℕ) (R : ℚ) :
    machineDiagonalBasisRowsCode (machineDiagonalBasisCanonicalInput d R) =
      rationalSquareMatrixRowsCode
        (rationalBallEllipsoid d 0 R).basis := by
  have hstate := congrArg machineDiagonalBasisMatrix
    (machineDiagonalBasisIterate_semantics d R d le_rfl)
  rw [machineDiagonalBasisRowsCode, machineDiagonalBasisFinalState]
  have hruler :
      (machineDiagonalBasisRuler
        (machineDiagonalBasisCanonicalInput d R)).length = d := by
    simp [machineDiagonalBasisRuler, machineDiagonalBasisCanonicalInput]
  rw [hruler]
  rw [hstate]
  simp only [machineDiagonalBasisCanonicalState,
    machineDiagonalBasisMatrix_pack]
  rw [rationalDiagonalPrefixMatrix_all]

/-! ## Complete ball state -/

/-- Input: `pair dimensionUnary radiusEntryCode`. -/
def machineRationalBallStateCode (word : List Bool) : List Bool :=
  pair (machineLengthBits (machineDiagonalBasisRuler word))
    (pair
      (machineRationalZeroVectorCode (machineDiagonalBasisRuler word))
      (machineDiagonalBasisRowsCode word))

theorem machineRationalBallStateCode_mem_FP :
    machineRationalBallStateCode ∈ FP := by
  have hdim := machineCompose_mem_FP machineDiagonalBasisRuler_mem_FP
    machineLengthBits_mem_FP
  have hcenter := machineCompose_mem_FP machineDiagonalBasisRuler_mem_FP
    machineRationalZeroVectorCode_mem_FP
  simpa only [machineRationalBallStateCode] using
    machinePair_mem_FP hdim
      (machinePair_mem_FP hcenter machineDiagonalBasisRowsCode_mem_FP)

@[simp] theorem machineRationalBallStateCode_encode (d : ℕ) (R : ℚ) :
    machineRationalBallStateCode (machineDiagonalBasisCanonicalInput d R) =
      rationalEllipsoidStateBinaryCode
        (rationalBallEllipsoid d 0 R) := by
  rw [machineRationalBallStateCode]
  simp only [machineDiagonalBasisRuler,
    machineDiagonalBasisCanonicalInput, machinePairFirst_pair,
    machineLengthBits_encode, List.length_replicate,
    machineRationalZeroVectorCode_encode,
    rationalEllipsoidStateBinaryCode, rationalBallEllipsoid_center]
  change pair d.bits
      (pair (rationalFiniteVectorCode (fun _ : Fin d ↦ (0 : ℚ)))
        (machineDiagonalBasisRowsCode
          (machineDiagonalBasisCanonicalInput d R))) = _
  rw [machineDiagonalBasisRowsCode_encode]
  rfl

end BeyondBethe
