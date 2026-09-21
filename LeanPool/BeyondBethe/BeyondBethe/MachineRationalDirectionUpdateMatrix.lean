/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalDirectionUpdateRow
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMatrixMul

/-!
# Polynomial-time direction-update matrices

This module maps the verified row constructor over all row indices.  The
result is the full rational matrix used to update an ellipsoid basis.
-/

namespace BeyondBethe

open Complexity

def rationalDirectionUpdateMatrix {d : ℕ} (b : Fin d → ℚ) :
    Matrix (Fin d) (Fin d) ℚ :=
  directionUpdateMatrix (rationalEllipsoidPerpScale d)
    (rationalEllipsoidParallelScale d) b

def rationalDirectionUpdateCanonicalWord {d : ℕ}
    (b : Fin d → ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair d.bits (rationalFiniteVectorCode b))

def rawDirectionDiagonalEntry {d : ℕ} (i j : Fin d) : RawRat :=
  if i = j then rawEllipsoidPerpScale d else RawRat.zero

def rawDirectionMatrixEntry {d : ℕ}
    (b : Fin d → ℚ) (i j : Fin d) : RawRat :=
  (rawDirectionDiagonalEntry i j).sub
    ((rawDirectionRowScale b i).mul (rawRatOfRat (b j)))

@[simp] theorem rawDirectionDiagonalEntry_value {d : ℕ}
    (i j : Fin d) :
    (rawDirectionDiagonalEntry i j).value =
      if i = j then rationalEllipsoidPerpScale d else 0 := by
  by_cases h : i = j
  · simp [rawDirectionDiagonalEntry, h]
  · simp [rawDirectionDiagonalEntry, h]

@[simp] theorem rawDirectionMatrixEntry_value {d : ℕ}
    (b : Fin d → ℚ) (i j : Fin d) :
    (rawDirectionMatrixEntry b i j).value =
      rationalDirectionUpdateMatrix b i j := by
  simp [rawDirectionMatrixEntry, rationalDirectionUpdateMatrix,
    directionUpdateMatrix, sub_eq_add_neg]

theorem rawEllipsoidDimension_width_le_direction_word {d : ℕ}
    (b : Fin d → ℚ) :
    rawRatWidth (rawEllipsoidDimension d) ≤
      (rationalDirectionUpdateCanonicalWord b).length := by
  have hsmall : rawRatWidth (rawEllipsoidDimension d) ≤ d + 1 := by
    simp [rawEllipsoidDimension, RawRat.ofNat, rawRatWidth]
    rw [Nat.size_le]
    have h := @Nat.lt_two_pow_self (d + 1)
    omega
  simp only [rationalDirectionUpdateCanonicalWord, pair_length,
    List.length_replicate] at hsmall ⊢
  omega

theorem rawDirection_b_width_le_word {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    rawRatWidth (rawRatOfRat (b i)) ≤
      (rationalDirectionUpdateCanonicalWord b).length := by
  have hcanonical := rawRatWidth_le_binaryCode_length (rawRatOfRat (b i))
  have helem := binaryListCode_element_length_le rationalEntryBinaryCode
    (show b i ∈ List.ofFn b by simp)
  have hvector :
      (rationalEntryBinaryCode (b i)).length ≤
        (rationalFiniteVectorCode b).length := by
    simpa only [rationalFiniteVectorCode] using helem
  rw [rawRatBinaryCode_rawRatOfRat] at hcanonical
  exact hcanonical.trans (hvector.trans (by
    change (rationalFiniteVectorCode b).length ≤
      (pair (List.replicate d true)
        (pair d.bits (rationalFiniteVectorCode b))).length
    rw [pair_length, pair_length]
    omega))

theorem rawDirectionNormSq_width_le_word {d : ℕ}
    (b : Fin d → ℚ) :
    rawRatWidth (rawDirectionNormSq b) ≤
      1 + 2 * (rationalDirectionUpdateCanonicalWord b).length := by
  let xs := List.ofFn b
  have hwidth := rawRatWidth_listDot_le RawRat.zero xs xs
  have hcost := rawRatListDotCost_le_codeLength xs xs
  have hcode :
      (binaryListCode rationalEntryBinaryCode xs).length ≤
        (rationalDirectionUpdateCanonicalWord b).length := by
    simp only [xs, rationalFiniteVectorCode,
      rationalDirectionUpdateCanonicalWord, pair_length,
      List.length_replicate]
    omega
  change rawRatWidth (rawRatListDot RawRat.zero xs xs) ≤ _
  rw [rawRatWidth_zero] at hwidth
  omega

theorem rawEllipsoidPerpScale_width_le_direction_word {d : ℕ}
    (b : Fin d → ℚ) :
    rawRatWidth (rawEllipsoidPerpScale d) ≤
      12 + 4 * (rationalDirectionUpdateCanonicalWord b).length := by
  let W := (rationalDirectionUpdateCanonicalWord b).length
  have hd := rawEllipsoidDimension_width_le_direction_word b
  have hdsq := rawRatWidth_mul_le
    (rawEllipsoidDimension d) (rawEllipsoidDimension d)
  have hfour := rawRatWidth_mul_le rawEllipsoidFour
    (rawEllipsoidDimensionSquare d)
  have halpha := rawRatWidth_div_le rawEllipsoidOne
    (rawEllipsoidFourDimensionSquare d)
  have halphaSq := rawRatWidth_mul_le
    (rawEllipsoidAlpha d) (rawEllipsoidAlpha d)
  have htwice := rawRatWidth_mul_le rawEllipsoidTwo
    (rawEllipsoidAlphaSquare d)
  have hperp := rawRatWidth_add_le rawEllipsoidOne
    (rawEllipsoidTwiceAlphaSquare d)
  have hone : rawRatWidth rawEllipsoidOne = 1 := by rfl
  have htwo : rawRatWidth rawEllipsoidTwo = 2 := by rfl
  have hfourWidth : rawRatWidth rawEllipsoidFour = 3 := by rfl
  have hd' : rawRatWidth (rawEllipsoidDimension d) ≤ W := by
    simpa only [W] using hd
  have hdsq0 : rawRatWidth (rawEllipsoidDimensionSquare d) ≤
      rawRatWidth (rawEllipsoidDimension d) +
        rawRatWidth (rawEllipsoidDimension d) := by
    simpa only [rawEllipsoidDimensionSquare] using hdsq
  have hdsq' : rawRatWidth (rawEllipsoidDimensionSquare d) ≤ 2 * W := by
    omega
  have hfour' : rawRatWidth (rawEllipsoidFourDimensionSquare d) ≤
      3 + 2 * W := by
    have hfour0 : rawRatWidth (rawEllipsoidFourDimensionSquare d) ≤
        rawRatWidth rawEllipsoidFour +
          rawRatWidth (rawEllipsoidDimensionSquare d) := by
      simpa only [rawEllipsoidFourDimensionSquare] using hfour
    omega
  have halpha' : rawRatWidth (rawEllipsoidAlpha d) ≤ 4 + 2 * W := by
    have halpha0 : rawRatWidth (rawEllipsoidAlpha d) ≤
        rawRatWidth rawEllipsoidOne +
          rawRatWidth (rawEllipsoidFourDimensionSquare d) := by
      simpa only [rawEllipsoidAlpha] using halpha
    omega
  have halphaSq' : rawRatWidth (rawEllipsoidAlphaSquare d) ≤
      8 + 4 * W := by
    have halphaSq0 : rawRatWidth (rawEllipsoidAlphaSquare d) ≤
        rawRatWidth (rawEllipsoidAlpha d) +
          rawRatWidth (rawEllipsoidAlpha d) := by
      simpa only [rawEllipsoidAlphaSquare] using halphaSq
    omega
  have htwice' : rawRatWidth (rawEllipsoidTwiceAlphaSquare d) ≤
      10 + 4 * W := by
    have htwice0 : rawRatWidth (rawEllipsoidTwiceAlphaSquare d) ≤
        rawRatWidth rawEllipsoidTwo +
          rawRatWidth (rawEllipsoidAlphaSquare d) := by
      simpa only [rawEllipsoidTwiceAlphaSquare] using htwice
    omega
  have hperp' : rawRatWidth (rawEllipsoidPerpScale d) ≤ 12 + 4 * W := by
    have hperp0 : rawRatWidth (rawEllipsoidPerpScale d) ≤
        rawRatWidth rawEllipsoidOne +
          rawRatWidth (rawEllipsoidTwiceAlphaSquare d) + 1 := by
      simpa only [rawEllipsoidPerpScale] using hperp
    omega
  simpa only [W] using hperp'

theorem rawEllipsoidParallelScale_width_le_direction_word {d : ℕ}
    (b : Fin d → ℚ) :
    rawRatWidth (rawEllipsoidParallelScale d) ≤
      6 + 3 * (rationalDirectionUpdateCanonicalWord b).length := by
  let W := (rationalDirectionUpdateCanonicalWord b).length
  have hd := rawEllipsoidDimension_width_le_direction_word b
  have hdsq := rawRatWidth_mul_le
    (rawEllipsoidDimension d) (rawEllipsoidDimension d)
  have hfour := rawRatWidth_mul_le rawEllipsoidFour
    (rawEllipsoidDimensionSquare d)
  have halpha := rawRatWidth_div_le rawEllipsoidOne
    (rawEllipsoidFourDimensionSquare d)
  have hover := rawRatWidth_div_le (rawEllipsoidAlpha d)
    (rawEllipsoidDimension d)
  have hparallel := rawRatWidth_sub_le rawEllipsoidOne
    (rawEllipsoidAlphaOverDimension d)
  have hone : rawRatWidth rawEllipsoidOne = 1 := by rfl
  have hfourWidth : rawRatWidth rawEllipsoidFour = 3 := by rfl
  have hd' : rawRatWidth (rawEllipsoidDimension d) ≤ W := by
    simpa only [W] using hd
  have hdsq0 : rawRatWidth (rawEllipsoidDimensionSquare d) ≤
      rawRatWidth (rawEllipsoidDimension d) +
        rawRatWidth (rawEllipsoidDimension d) := by
    simpa only [rawEllipsoidDimensionSquare] using hdsq
  have hdsq' : rawRatWidth (rawEllipsoidDimensionSquare d) ≤ 2 * W := by
    omega
  have hfour' : rawRatWidth (rawEllipsoidFourDimensionSquare d) ≤
      3 + 2 * W := by
    have hfour0 : rawRatWidth (rawEllipsoidFourDimensionSquare d) ≤
        rawRatWidth rawEllipsoidFour +
          rawRatWidth (rawEllipsoidDimensionSquare d) := by
      simpa only [rawEllipsoidFourDimensionSquare] using hfour
    omega
  have halpha' : rawRatWidth (rawEllipsoidAlpha d) ≤ 4 + 2 * W := by
    have halpha0 : rawRatWidth (rawEllipsoidAlpha d) ≤
        rawRatWidth rawEllipsoidOne +
          rawRatWidth (rawEllipsoidFourDimensionSquare d) := by
      simpa only [rawEllipsoidAlpha] using halpha
    omega
  have hover' : rawRatWidth (rawEllipsoidAlphaOverDimension d) ≤
      4 + 3 * W := by
    have hover0 : rawRatWidth (rawEllipsoidAlphaOverDimension d) ≤
        rawRatWidth (rawEllipsoidAlpha d) +
          rawRatWidth (rawEllipsoidDimension d) := by
      simpa only [rawEllipsoidAlphaOverDimension] using hover
    omega
  have hparallel' : rawRatWidth (rawEllipsoidParallelScale d) ≤
      6 + 3 * W := by
    have hparallel0 : rawRatWidth (rawEllipsoidParallelScale d) ≤
        rawRatWidth rawEllipsoidOne +
          rawRatWidth (rawEllipsoidAlphaOverDimension d) + 1 := by
      simpa only [rawEllipsoidParallelScale] using hparallel
    omega
  simpa only [W] using hparallel'

theorem rawDirectionMatrixEntry_width_le_word {d : ℕ}
    (b : Fin d → ℚ) (i j : Fin d) :
    rawRatWidth (rawDirectionMatrixEntry b i j) ≤
      33 + 15 * (rationalDirectionUpdateCanonicalWord b).length := by
  let W := (rationalDirectionUpdateCanonicalWord b).length
  have hperp := rawEllipsoidPerpScale_width_le_direction_word b
  have hparallel := rawEllipsoidParallelScale_width_le_direction_word b
  have hnorm := rawDirectionNormSq_width_le_word b
  have hbi := rawDirection_b_width_le_word b i
  have hbj := rawDirection_b_width_le_word b j
  have hperp' : rawRatWidth (rawEllipsoidPerpScale d) ≤ 12 + 4 * W := by
    simpa only [W] using hperp
  have hparallel' : rawRatWidth (rawEllipsoidParallelScale d) ≤
      6 + 3 * W := by simpa only [W] using hparallel
  have hnorm' : rawRatWidth (rawDirectionNormSq b) ≤ 1 + 2 * W := by
    simpa only [W] using hnorm
  have hbi' : rawRatWidth (rawRatOfRat (b i)) ≤ W := by
    simpa only [W] using hbi
  have hbj' : rawRatWidth (rawRatOfRat (b j)) ≤ W := by
    simpa only [W] using hbj
  have hgap' : rawRatWidth (rawDirectionGap d) ≤ 19 + 7 * W := by
    calc
      _ = rawRatWidth ((rawEllipsoidPerpScale d).sub
          (rawEllipsoidParallelScale d)) := rfl
      _ ≤ rawRatWidth (rawEllipsoidPerpScale d) +
          rawRatWidth (rawEllipsoidParallelScale d) + 1 :=
        rawRatWidth_sub_le _ _
      _ ≤ 19 + 7 * W := by omega
  have hcoeff' : rawRatWidth (rawDirectionCoefficient b) ≤
      20 + 9 * W := by
    calc
      _ = rawRatWidth ((rawDirectionGap d).div
          (rawDirectionNormSq b)) := rfl
      _ ≤ rawRatWidth (rawDirectionGap d) +
          rawRatWidth (rawDirectionNormSq b) := rawRatWidth_div_le _ _
      _ ≤ 20 + 9 * W := by omega
  have hrowScale' : rawRatWidth (rawDirectionRowScale b i) ≤
      20 + 10 * W := by
    calc
      _ = rawRatWidth ((rawDirectionCoefficient b).mul
          (rawRatOfRat (b i))) := rfl
      _ ≤ rawRatWidth (rawDirectionCoefficient b) +
          rawRatWidth (rawRatOfRat (b i)) := rawRatWidth_mul_le _ _
      _ ≤ 20 + 10 * W := by omega
  have hproduct' : rawRatWidth
      ((rawDirectionRowScale b i).mul (rawRatOfRat (b j))) ≤
        20 + 11 * W := by
    exact (rawRatWidth_mul_le _ _).trans (by omega)
  have hdiag : rawRatWidth (rawDirectionDiagonalEntry i j) ≤
      12 + 4 * W := by
    by_cases hij : i = j
    · simpa only [rawDirectionDiagonalEntry, hij, if_true] using hperp
    · simp only [rawDirectionDiagonalEntry, hij, ite_false, rawRatWidth_zero]
      omega
  calc
    _ = rawRatWidth ((rawDirectionDiagonalEntry i j).sub
        ((rawDirectionRowScale b i).mul (rawRatOfRat (b j)))) := rfl
    _ ≤ rawRatWidth (rawDirectionDiagonalEntry i j) +
        rawRatWidth ((rawDirectionRowScale b i).mul
          (rawRatOfRat (b j))) + 1 := rawRatWidth_sub_le _ _
    _ ≤ 33 + 15 * W := by omega

theorem rationalDirectionMatrix_entry_code_length_le {d : ℕ}
    (b : Fin d → ℚ) (i j : Fin d) :
    (rationalEntryBinaryCode (rationalDirectionUpdateMatrix b i j)).length ≤
      1252 + 540 * (rationalDirectionUpdateCanonicalWord b).length := by
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (rawDirectionMatrixEntry b i j)
  rw [binaryNormalizeRawRat_eq_value,
    rawDirectionMatrixEntry_value] at hcanonical
  have hwidth := rawDirectionMatrixEntry_width_le_word b i j
  exact hcanonical.trans (by nlinarith)

def machineRationalDirectionUpdateMatrixInputBound
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineRationalDirectionUpdateMatrixInputBound_mem_FP :
    machineRationalDirectionUpdateMatrixInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem rationalDirectionUpdateMatrix_code_length_le_cubic {d : ℕ}
    (b : Fin d → ℚ) :
    (rationalSquareMatrixRowsCode
      (rationalDirectionUpdateMatrix b)).length ≤
      d * (2 * (d *
        (2 * (1252 + 540 *
          (rationalDirectionUpdateCanonicalWord b).length) + 2)) + 2) := by
  let L := 1252 + 540 * (rationalDirectionUpdateCanonicalWord b).length
  have hentry : ∀ i j : Fin d,
      (rationalEntryBinaryCode
        (rationalDirectionUpdateMatrix b i j)).length ≤ L := by
    intro i j
    exact rationalDirectionMatrix_entry_code_length_le b i j
  rw [rationalSquareMatrixRowsCode, binaryListCode_length_eq_sum]
  simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  calc
    (∑ i : Fin d,
        (2 * (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j)).length +
          2)) ≤
      ∑ _i : Fin d, (2 * (d * (2 * L + 2)) + 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        rw [binaryListCode_length_eq_sum]
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
        calc
          (∑ j : Fin d,
              (2 * (rationalEntryBinaryCode
                (rationalDirectionUpdateMatrix b i j)).length + 2)) ≤
            ∑ _j : Fin d, (2 * L + 2) := by
              apply Finset.sum_le_sum
              intro j _
              have h := hentry i j
              omega
          _ = d * (2 * L + 2) := by simp
    _ = d * (2 * (d * (2 * L + 2)) + 2) := by simp

theorem rationalDirectionUpdateMatrix_code_length_le_bound {d : ℕ}
    (b : Fin d → ℚ) :
    (rationalSquareMatrixRowsCode
      (rationalDirectionUpdateMatrix b)).length ≤
      (machineRationalDirectionUpdateMatrixInputBound
        (rationalDirectionUpdateCanonicalWord b)).length := by
  let word := rationalDirectionUpdateCanonicalWord b
  let n := word.length
  let x := 16 + n
  let y := 16 + x ^ 2
  let z := 16 + y ^ 2
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalDirectionUpdateCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using h
  have hn4 : 4 ≤ n := by
    simp only [n, word, rationalDirectionUpdateCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hcubic := rationalDirectionUpdateMatrix_code_length_le_cubic b
  have hd' : d ≤ n := by simpa only [n] using hd
  have hdn : d * n ≤ n * n := Nat.mul_le_mul hd' le_rfl
  have hdd : d * d ≤ n * n := Nat.mul_le_mul hd' hd'
  have hddn : (d * d) * n ≤ (n * n) * n :=
    Nat.mul_le_mul hdd le_rfl
  have hpoly :
      d * (2 * (d * (2 * (1252 + 540 * n) + 2)) + 2) ≤
        4000 * n ^ 3 := by
    nlinarith
  have hout :
      (rationalSquareMatrixRowsCode
        (rationalDirectionUpdateMatrix b)).length ≤ 4000 * n ^ 3 := by
    apply hcubic.trans
    simpa only [n, word] using hpoly
  have hnx : n ≤ x := by simp [x]
  have hxpos : 0 < x := by omega
  have h4000 : 4000 ≤ x ^ 3 := by
    dsimp only [x]
    nlinarith
  have hnx3 : n ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hnx 3
  have hto6 : 4000 * n ^ 3 ≤ x ^ 6 := by
    have h := Nat.mul_le_mul h4000 hnx3
    simpa only [← pow_add] using h
  have hto8 : x ^ 6 ≤ x ^ 8 :=
    Nat.pow_le_pow_right hxpos (by omega)
  have hxy : x ^ 2 ≤ y := by simp [y]
  have hx4y2 : x ^ 4 ≤ y ^ 2 := by
    have h := Nat.pow_le_pow_left hxy 2
    simpa only [← pow_mul] using h
  have hyz : y ^ 2 ≤ z := by simp [z]
  have hx4z : x ^ 4 ≤ z := hx4y2.trans hyz
  have hx8z2 : x ^ 8 ≤ z ^ 2 := by
    have h := Nat.pow_le_pow_left hx4z 2
    simpa only [← pow_mul] using h
  apply hout.trans
  apply hto6.trans
  apply hto8.trans
  apply hx8z2.trans_eq
  simp only [machineRationalDirectionUpdateMatrixInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, n, x, y, z, word, pow_two]

/-! ## Bounded outer row scan -/

def machineRationalDirectionUpdateMatrixIndices
    (word : List Bool) : List Bool :=
  machineUnaryRangeCode (machinePairFirst word)

def machineRationalDirectionUpdateMatrixCurrentRow
    (state : List Bool) : List Bool :=
  machineRationalDirectionUpdateRowCode
    (pair (machineRationalTransposeMulVectorCurrentIndex state)
      (machineRationalTransposeMulVectorStatePayload state))

def machineRationalDirectionUpdateMatrixCandidate
    (state : List Bool) : List Bool :=
  pair (machineRationalDirectionUpdateMatrixCurrentRow state)
    (machineRationalTransposeMulVectorAccumulator state)

def machineRationalDirectionUpdateMatrixNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalDirectionUpdateMatrixCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

def machineRationalDirectionUpdateMatrixAdvance
    (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineRationalDirectionUpdateMatrixNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

def machineRationalDirectionUpdateMatrixStep
    (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineRationalDirectionUpdateMatrixAdvance state)

def machineRationalDirectionUpdateMatrixInit
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineRationalDirectionUpdateMatrixIndices word) [] word
    (machineRationalDirectionUpdateMatrixInputBound word)

def machineRationalDirectionUpdateMatrixWidth
    (word : List Bool) : List Bool :=
  let bound := machineRationalDirectionUpdateMatrixInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

def machineRationalDirectionUpdateMatrixFinalState
    (word : List Bool) : List Bool :=
  (machineRationalDirectionUpdateMatrixStep)^[word.length]
    (machineRationalDirectionUpdateMatrixInit word)

def machineRationalDirectionUpdateMatrixReversedCode
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineRationalDirectionUpdateMatrixFinalState word)

/-- Input: `pair dimensionUnary (pair dimensionBits vectorCode)`. -/
def machineRationalDirectionUpdateMatrixCode
    (word : List Bool) : List Bool :=
  machineListReverse
    (machineRationalDirectionUpdateMatrixReversedCode word)

theorem machineRationalDirectionUpdateMatrixIndices_mem_FP :
    machineRationalDirectionUpdateMatrixIndices ∈ FP := by
  simpa only [machineRationalDirectionUpdateMatrixIndices] using
    machineCompose_mem_FP machinePairFirst_mem_FP
      machineUnaryRangeCode_mem_FP

theorem machineRationalDirectionUpdateMatrixCurrentRow_mem_FP :
    machineRationalDirectionUpdateMatrixCurrentRow ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalTransposeMulVectorCurrentIndex_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP
  simpa only [machineRationalDirectionUpdateMatrixCurrentRow] using
    machineCompose_mem_FP hinput
      machineRationalDirectionUpdateRowCode_mem_FP

theorem machineRationalDirectionUpdateMatrixCandidate_mem_FP :
    machineRationalDirectionUpdateMatrixCandidate ∈ FP :=
  machinePair_mem_FP machineRationalDirectionUpdateMatrixCurrentRow_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalDirectionUpdateMatrixNextAccumulator_mem_FP :
    machineRationalDirectionUpdateMatrixNextAccumulator ∈ FP := by
  simpa only [machineRationalDirectionUpdateMatrixNextAccumulator] using
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineRationalDirectionUpdateMatrixCandidate_mem_FP

theorem machineRationalDirectionUpdateMatrixAdvance_mem_FP :
    machineRationalDirectionUpdateMatrixAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP
      machineRationalDirectionUpdateMatrixNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineRationalDirectionUpdateMatrixStep_mem_FP :
    machineRationalDirectionUpdateMatrixStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineRationalDirectionUpdateMatrixAdvance_mem_FP

theorem machineRationalDirectionUpdateMatrixInit_mem_FP :
    machineRationalDirectionUpdateMatrixInit ∈ FP := by
  exact machinePair_mem_FP
    machineRationalDirectionUpdateMatrixIndices_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP id_mem_FP
        machineRationalDirectionUpdateMatrixInputBound_mem_FP))

theorem machineRationalDirectionUpdateMatrixWidth_mem_FP :
    machineRationalDirectionUpdateMatrixWidth ∈ FP := by
  have hbound := machineRationalDirectionUpdateMatrixInputBound_mem_FP
  exact machinePair_mem_FP hbound
    (machinePair_mem_FP hbound (machinePair_mem_FP hbound hbound))

theorem machineRationalDirectionUpdateMatrixInit_bound
    (word : List Bool) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalDirectionUpdateMatrixInit word) := by
  simp only [MachineRationalTransposeMulVectorStateBound,
    machineRationalDirectionUpdateMatrixInit,
    machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalDirectionUpdateMatrixInputBound]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineRationalDirectionUpdateMatrixIndices,
      machineRationalTransposeMulVectorIndices,
      machineRationalTransposeMulVectorDimension] using
        machineRationalTransposeMulVector_indices_le_bound word
  · exact machineRationalTransposeMulVector_word_le_bound word

theorem machineRationalDirectionUpdateMatrixStep_bound
    {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalDirectionUpdateMatrixStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineRationalDirectionUpdateMatrixStep, hnil,
      machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineRationalDirectionUpdateMatrixStep, hcode,
          machineIfEmpty_cons,
          machineRationalDirectionUpdateMatrixAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineRationalDirectionUpdateMatrixNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalDirectionUpdateMatrixIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineRationalDirectionUpdateMatrixStep)^[k]
        (machineRationalDirectionUpdateMatrixInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalDirectionUpdateMatrixInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalDirectionUpdateMatrixStep_bound ih

theorem machineRationalDirectionUpdateMatrixIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalDirectionUpdateMatrixStep)^[iterations]
      (machineRationalDirectionUpdateMatrixInit word)).length ≤
        (machineRationalDirectionUpdateMatrixWidth word).length := by
  rcases machineRationalDirectionUpdateMatrixIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineRationalDirectionUpdateMatrixWidth,
    machineRationalDirectionUpdateMatrixInputBound, pair_length]
  omega

theorem machineRationalDirectionUpdateMatrixFinalState_mem_FP :
    machineRationalDirectionUpdateMatrixFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP
    machineRationalDirectionUpdateMatrixStep_mem_FP
    machineRationalDirectionUpdateMatrixInit_mem_FP id_mem_FP
    machineRationalDirectionUpdateMatrixWidth_mem_FP
    machineRationalDirectionUpdateMatrixIterate_length_le_width

theorem machineRationalDirectionUpdateMatrixReversedCode_mem_FP :
    machineRationalDirectionUpdateMatrixReversedCode ∈ FP := by
  simpa only [machineRationalDirectionUpdateMatrixReversedCode] using
    machineCompose_mem_FP
      machineRationalDirectionUpdateMatrixFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalDirectionUpdateMatrixCode_mem_FP :
    machineRationalDirectionUpdateMatrixCode ∈ FP := by
  simpa only [machineRationalDirectionUpdateMatrixCode] using
    machineCompose_mem_FP
      machineRationalDirectionUpdateMatrixReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact scan semantics -/

def rationalDirectionUpdateRowsPrefix {d : ℕ}
    (b : Fin d → ℚ) (k : ℕ) : List (List ℚ) :=
  ((List.finRange d).take k).map
    fun i ↦ List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j

def machineRationalDirectionUpdateMatrixSemanticState {d : ℕ}
    (b : Fin d → ℚ) (k : ℕ) : List Bool :=
  let word := rationalDirectionUpdateCanonicalWord b
  machineRationalTransposeMulVectorPack
    (binaryListCode finUnaryCode ((List.finRange d).drop k))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rationalDirectionUpdateRowsPrefix b k).reverse)
    word (machineRationalDirectionUpdateMatrixInputBound word)

theorem machineRationalDirectionUpdateMatrixInit_semantics {d : ℕ}
    (b : Fin d → ℚ) :
    machineRationalDirectionUpdateMatrixInit
        (rationalDirectionUpdateCanonicalWord b) =
      machineRationalDirectionUpdateMatrixSemanticState b 0 := by
  simp [machineRationalDirectionUpdateMatrixInit,
    machineRationalDirectionUpdateMatrixSemanticState,
    machineRationalDirectionUpdateMatrixIndices,
    rationalDirectionUpdateCanonicalWord,
    machineUnaryRangeCode_encode, finRangeUnaryCode,
    rationalDirectionUpdateRowsPrefix, binaryListCode]

theorem rationalDirectionUpdateRowsPrefix_succ {d : ℕ}
    (b : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    rationalDirectionUpdateRowsPrefix b (k + 1) =
      rationalDirectionUpdateRowsPrefix b k ++
        [List.ofFn fun j ↦ rationalDirectionUpdateMatrix b ⟨k, hk⟩ j] := by
  simp only [rationalDirectionUpdateRowsPrefix, List.map_take]
  have hkm : k < (List.finRange d).length := by simpa
  simpa [List.getElem_finRange] using
    congrArg (List.map fun i ↦
      List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j)
      (List.take_concat_get hkm).symm

theorem machineRationalDirectionUpdateMatrixStep_semantics {d : ℕ}
    (b : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    machineRationalDirectionUpdateMatrixStep
        (machineRationalDirectionUpdateMatrixSemanticState b k) =
      machineRationalDirectionUpdateMatrixSemanticState b (k + 1) := by
  let word := rationalDirectionUpdateCanonicalWord b
  let i : Fin d := ⟨k, hk⟩
  have hdrop :
      (List.finRange d).drop k =
        i :: (List.finRange d).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.finRange d).length by simpa) using 1
    simp [i, List.getElem_finRange]
  have hprefix := rationalDirectionUpdateRowsPrefix_succ b k hk
  have hreverse :
      (rationalDirectionUpdateRowsPrefix b (k + 1)).reverse =
        (List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j) ::
          (rationalDirectionUpdateRowsPrefix b k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [i]
  have hcand :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalDirectionUpdateRowsPrefix b (k + 1)).reverse).length ≤
        (machineRationalDirectionUpdateMatrixInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows (rationalDirectionUpdateMatrix b)) (k + 1)
    have hprefixEq : rationalDirectionUpdateRowsPrefix b (k + 1) =
        (rationalMatrixRows
          (rationalDirectionUpdateMatrix b)).take (k + 1) := by
      apply List.ext_getElem
      · simp [rationalDirectionUpdateRowsPrefix, rationalMatrixRows]
      · intro r hrLeft hrRight
        simp [rationalDirectionUpdateRowsPrefix, rationalMatrixRows,
          List.getElem_finRange]
    rw [hprefixEq]
    exact hprefixBound.trans
      (rationalDirectionUpdateMatrix_code_length_le_bound b)
  have hcandPair :
      (pair
        (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalDirectionUpdateRowsPrefix b k).reverse)).length ≤
        (machineRationalDirectionUpdateMatrixInputBound word).length := by
    simpa only [hreverse, binaryListCode] using hcand
  have hnonempty :
      binaryListCode finUnaryCode ((List.finRange d).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil finUnaryCode i
      ((List.finRange d).drop (k + 1))
  rw [machineRationalDirectionUpdateMatrixStep]
  simp only [machineRationalDirectionUpdateMatrixSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalDirectionUpdateMatrixAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalDirectionUpdateMatrixNextAccumulator,
    machineRationalDirectionUpdateMatrixCandidate,
    machineRationalDirectionUpdateMatrixCurrentRow,
    machineRationalTransposeMulVectorCurrentIndex]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineRationalDirectionUpdateRowCode
          (pair (finUnaryCode i) word))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalDirectionUpdateRowsPrefix b k).reverse)).take
        (machineRationalDirectionUpdateMatrixInputBound word).length) _ _ = _
  dsimp only [word, rationalDirectionUpdateCanonicalWord]
  rw [show finUnaryCode i = List.replicate i.1 true by rfl,
    machineRationalDirectionUpdateRowCode_encode]
  change machineRationalTransposeMulVectorPack _
      ((pair (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalDirectionUpdateMatrix b i j))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalDirectionUpdateRowsPrefix b k).reverse)).take
        (machineRationalDirectionUpdateMatrixInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineRationalDirectionUpdateMatrixIterate_semantics {d : ℕ}
    (b : Fin d → ℚ) : ∀ k ≤ d,
    (machineRationalDirectionUpdateMatrixStep)^[k]
      (machineRationalDirectionUpdateMatrixInit
        (rationalDirectionUpdateCanonicalWord b)) =
      machineRationalDirectionUpdateMatrixSemanticState b k := by
  intro k hk
  induction k with
  | zero => exact machineRationalDirectionUpdateMatrixInit_semantics b
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalDirectionUpdateMatrixStep_semantics b k (by omega)

theorem machineRationalDirectionUpdateMatrix_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalDirectionUpdateMatrixStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalDirectionUpdateMatrixStep]

theorem rationalDirectionUpdateRowsPrefix_all {d : ℕ}
    (b : Fin d → ℚ) :
    rationalDirectionUpdateRowsPrefix b d =
      rationalMatrixRows (rationalDirectionUpdateMatrix b) := by
  apply List.ext_getElem
  · simp [rationalDirectionUpdateRowsPrefix, rationalMatrixRows]
  · intro i hiLeft hiRight
    simp [rationalDirectionUpdateRowsPrefix, rationalMatrixRows,
      List.getElem_finRange]

theorem machineRationalDirectionUpdateMatrixReversedCode_encode {d : ℕ}
    (b : Fin d → ℚ) :
    machineRationalDirectionUpdateMatrixReversedCode
        (rationalDirectionUpdateCanonicalWord b) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows (rationalDirectionUpdateMatrix b)).reverse := by
  let word := rationalDirectionUpdateCanonicalWord b
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalDirectionUpdateCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using h
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineRationalDirectionUpdateMatrixReversedCode word = _
  rw [machineRationalDirectionUpdateMatrixReversedCode,
    machineRationalDirectionUpdateMatrixFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalDirectionUpdateMatrixIterate_semantics b d le_rfl]
  simp only [machineRationalDirectionUpdateMatrixSemanticState]
  rw [show binaryListCode finUnaryCode ((List.finRange d).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineRationalDirectionUpdateMatrix_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [rationalDirectionUpdateRowsPrefix_all]

@[simp] theorem machineRationalDirectionUpdateMatrixCode_encode {d : ℕ}
    (b : Fin d → ℚ) :
    machineRationalDirectionUpdateMatrixCode
        (rationalDirectionUpdateCanonicalWord b) =
      rationalSquareMatrixRowsCode (rationalDirectionUpdateMatrix b) := by
  rw [machineRationalDirectionUpdateMatrixCode,
    machineRationalDirectionUpdateMatrixReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
