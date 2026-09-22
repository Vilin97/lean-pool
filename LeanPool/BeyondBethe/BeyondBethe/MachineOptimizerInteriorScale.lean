/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerMatrixBitBound
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalPower
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateExpGuard
import LeanPool.BeyondBethe.BeyondBethe.ExplicitOptimizerScales

/-!
# Finite-word interior scale for the Bethe optimizer

The optimizer uses a dyadic lower bound on every matrix coordinate.  Its
exponent is computed in binary and expanded to unary only behind an explicit
degree-64 guard in the source matrix length.  Thus this file does not hide an
unrestricted binary-to-unary conversion.
-/

namespace BeyondBethe

open Complexity

/-! ## Raw rational expression computed by the machine -/

def rawOptimizerTwo : RawRat := RawRat.ofNat 2

def rawOptimizerFour : RawRat := RawRat.ofNat 4

def rawOptimizerHalf : RawRat :=
  (RawRat.ofNat 1).div rawOptimizerTwo

def rawOptimizerXi : RawRat := rawRatOfRat explicitXi

def rawOptimizerDimension (n : ℕ) : RawRat := RawRat.ofNat n

def rawOptimizerBitBound (B : ℕ) : RawRat := RawRat.ofNat B

def rawOptimizerTau (n : ℕ) : RawRat :=
  rawOptimizerXi.div (rawOptimizerFour.mul (rawOptimizerDimension n))

def rawOptimizerNSquare (n : ℕ) : RawRat :=
  (rawOptimizerDimension n).mul (rawOptimizerDimension n)

def rawOptimizerNCube (n : ℕ) : RawRat :=
  (rawOptimizerNSquare n).mul (rawOptimizerDimension n)

def rawOptimizerInteriorSum (n B : ℕ) : RawRat :=
  ((rawOptimizerDimension n).mul (rawOptimizerBitBound B)).add
    (rawOptimizerTwo.mul (rawOptimizerNSquare n))

def rawOptimizerInteriorK0 (n B : ℕ) : RawRat :=
  ((rawOptimizerDimension n).mul (rawOptimizerInteriorSum n B)).div
      (rawOptimizerTau n) |>.add (rawOptimizerNCube n)

def rawOptimizerTwiceInteriorK0 (n B : ℕ) : RawRat :=
  rawOptimizerTwo.mul (rawOptimizerInteriorK0 n B)

/-! ## Binary machines for the expression -/

def machineOptimizerDimensionBits (word : List Bool) : List Bool :=
  machineMatrixDimensionWord word

def machineOptimizerDimensionUnary (word : List Bool) : List Bool :=
  machineMatrixDimensionUnary word

def machineOptimizerDimensionRawCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineOptimizerDimensionBits word)) [true]

def machineOptimizerBitBoundBits (word : List Bool) : List Bool :=
  machineLengthBits (machineMatrixEntryBitBoundRuler word)

def machineOptimizerBitBoundRawCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineOptimizerBitBoundBits word)) [true]

def machineOptimizerFourDimensionRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerFour)
      (machineOptimizerDimensionRawCode word))

def machineOptimizerTauRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode rawOptimizerXi)
      (machineOptimizerFourDimensionRawCode word))

def machineOptimizerNSquareRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerDimensionRawCode word)
      (machineOptimizerDimensionRawCode word))

def machineOptimizerNCubeRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerNSquareRawCode word)
      (machineOptimizerDimensionRawCode word))

def machineOptimizerNBProductRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerDimensionRawCode word)
      (machineOptimizerBitBoundRawCode word))

def machineOptimizerTwiceNSquareRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineOptimizerNSquareRawCode word))

def machineOptimizerInteriorSumRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerNBProductRawCode word)
      (machineOptimizerTwiceNSquareRawCode word))

def machineOptimizerNTimesInteriorSumRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerDimensionRawCode word)
      (machineOptimizerInteriorSumRawCode word))

def machineOptimizerInteriorQuotientRawCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineOptimizerNTimesInteriorSumRawCode word)
      (machineOptimizerTauRawCode word))

def machineOptimizerInteriorK0RawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerInteriorQuotientRawCode word)
      (machineOptimizerNCubeRawCode word))

def machineOptimizerTwiceInteriorK0RawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineOptimizerInteriorK0RawCode word))

def machineOptimizerInteriorExponentBits (word : List Bool) : List Bool :=
  machineRationalCeilNatBits
    (machineOptimizerTwiceInteriorK0RawCode word)

/-! ## Polynomial-time closure -/

theorem machineOptimizerDimensionBits_mem_FP :
    machineOptimizerDimensionBits ∈ FP :=
  machineMatrixDimensionWord_mem_FP

theorem machineOptimizerDimensionUnary_mem_FP :
    machineOptimizerDimensionUnary ∈ FP :=
  machineMatrixDimensionUnary_mem_FP

theorem machineOptimizerDimensionRawCode_mem_FP :
    machineOptimizerDimensionRawCode ∈ FP := by
  exact machinePair_mem_FP
    (machineCompose_mem_FP machineOptimizerDimensionBits_mem_FP
      machineNaturalIntegerCode_mem_FP)
    (machineConst_mem_FP [true])

theorem machineOptimizerBitBoundBits_mem_FP :
    machineOptimizerBitBoundBits ∈ FP := by
  simpa only [machineOptimizerBitBoundBits] using!
    machineCompose_mem_FP machineMatrixEntryBitBoundRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineOptimizerBitBoundRawCode_mem_FP :
    machineOptimizerBitBoundRawCode ∈ FP := by
  exact machinePair_mem_FP
    (machineCompose_mem_FP machineOptimizerBitBoundBits_mem_FP
      machineNaturalIntegerCode_mem_FP)
    (machineConst_mem_FP [true])

theorem machineOptimizerFourDimensionRawCode_mem_FP :
    machineOptimizerFourDimensionRawCode ∈ FP := by
  simpa only [machineOptimizerFourDimensionRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerFour))
      machineOptimizerDimensionRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerTauRawCode_mem_FP :
    machineOptimizerTauRawCode ∈ FP := by
  simpa only [machineOptimizerTauRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerXi))
      machineOptimizerFourDimensionRawCode_mem_FP)
    machineRawRatDivCode_mem_FP

theorem machineOptimizerNSquareRawCode_mem_FP :
    machineOptimizerNSquareRawCode ∈ FP := by
  simpa only [machineOptimizerNSquareRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerDimensionRawCode_mem_FP
      machineOptimizerDimensionRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerNCubeRawCode_mem_FP :
    machineOptimizerNCubeRawCode ∈ FP := by
  simpa only [machineOptimizerNCubeRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerNSquareRawCode_mem_FP
      machineOptimizerDimensionRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerNBProductRawCode_mem_FP :
    machineOptimizerNBProductRawCode ∈ FP := by
  simpa only [machineOptimizerNBProductRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerDimensionRawCode_mem_FP
      machineOptimizerBitBoundRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerTwiceNSquareRawCode_mem_FP :
    machineOptimizerTwiceNSquareRawCode ∈ FP := by
  simpa only [machineOptimizerTwiceNSquareRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
      machineOptimizerNSquareRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerInteriorSumRawCode_mem_FP :
    machineOptimizerInteriorSumRawCode ∈ FP := by
  simpa only [machineOptimizerInteriorSumRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerNBProductRawCode_mem_FP
      machineOptimizerTwiceNSquareRawCode_mem_FP)
    machineRawRatAddCode_mem_FP

theorem machineOptimizerNTimesInteriorSumRawCode_mem_FP :
    machineOptimizerNTimesInteriorSumRawCode ∈ FP := by
  simpa only [machineOptimizerNTimesInteriorSumRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerDimensionRawCode_mem_FP
      machineOptimizerInteriorSumRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerInteriorQuotientRawCode_mem_FP :
    machineOptimizerInteriorQuotientRawCode ∈ FP := by
  simpa only [machineOptimizerInteriorQuotientRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerNTimesInteriorSumRawCode_mem_FP
      machineOptimizerTauRawCode_mem_FP)
    machineRawRatDivCode_mem_FP

theorem machineOptimizerInteriorK0RawCode_mem_FP :
    machineOptimizerInteriorK0RawCode ∈ FP := by
  simpa only [machineOptimizerInteriorK0RawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerInteriorQuotientRawCode_mem_FP
      machineOptimizerNCubeRawCode_mem_FP)
    machineRawRatAddCode_mem_FP

theorem machineOptimizerTwiceInteriorK0RawCode_mem_FP :
    machineOptimizerTwiceInteriorK0RawCode ∈ FP := by
  simpa only [machineOptimizerTwiceInteriorK0RawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
      machineOptimizerInteriorK0RawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerInteriorExponentBits_mem_FP :
    machineOptimizerInteriorExponentBits ∈ FP := by
  simpa only [machineOptimizerInteriorExponentBits] using!
    machineCompose_mem_FP machineOptimizerTwiceInteriorK0RawCode_mem_FP
      machineRationalCeilNatBits_mem_FP

/-! ## Exact semantics on canonical matrix words -/

@[simp] theorem machineOptimizerDimensionBits_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerDimensionBits
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) = n.bits := by
  simp [machineOptimizerDimensionBits]

@[simp] theorem machineOptimizerDimensionUnary_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerDimensionUnary
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate n true := by
  simp [machineOptimizerDimensionUnary]

@[simp] theorem machineOptimizerDimensionRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerDimensionRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerDimension n) := by
  rw [machineOptimizerDimensionRawCode,
    machineOptimizerDimensionBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [rawOptimizerDimension, RawRat.ofNat, rawRatBinaryCode]

@[simp] theorem machineOptimizerBitBoundBits_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerBitBoundBits
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      (rationalMatrixEntryBitBound A).bits := by
  simp [machineOptimizerBitBoundBits]

@[simp] theorem machineOptimizerBitBoundRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerBitBoundRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerBitBound
        (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerBitBoundRawCode,
    machineOptimizerBitBoundBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [rawOptimizerBitBound, RawRat.ofNat, rawRatBinaryCode]

@[simp] theorem machineOptimizerFourDimensionRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerFourDimensionRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerFour.mul (rawOptimizerDimension n)) := by
  rw [machineOptimizerFourDimensionRawCode,
    machineOptimizerDimensionRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerTauRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTauRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerTau n) := by
  rw [machineOptimizerTauRawCode,
    machineOptimizerFourDimensionRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineOptimizerNSquareRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerNSquareRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerNSquare n) := by
  rw [machineOptimizerNSquareRawCode,
    machineOptimizerDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineOptimizerNCubeRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerNCubeRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerNCube n) := by
  rw [machineOptimizerNCubeRawCode,
    machineOptimizerNSquareRawCode_encode,
    machineOptimizerDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineOptimizerNBProductRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerNBProductRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode ((rawOptimizerDimension n).mul
        (rawOptimizerBitBound (rationalMatrixEntryBitBound A))) := by
  rw [machineOptimizerNBProductRawCode,
    machineOptimizerDimensionRawCode_encode,
    machineOptimizerBitBoundRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerTwiceNSquareRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTwiceNSquareRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerTwo.mul (rawOptimizerNSquare n)) := by
  rw [machineOptimizerTwiceNSquareRawCode,
    machineOptimizerNSquareRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerInteriorSumRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorSumRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerInteriorSum n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerInteriorSumRawCode,
    machineOptimizerNBProductRawCode_encode,
    machineOptimizerTwiceNSquareRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerNTimesInteriorSumRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerNTimesInteriorSumRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode ((rawOptimizerDimension n).mul
        (rawOptimizerInteriorSum n (rationalMatrixEntryBitBound A))) := by
  rw [machineOptimizerNTimesInteriorSumRawCode,
    machineOptimizerDimensionRawCode_encode,
    machineOptimizerInteriorSumRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerInteriorQuotientRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorQuotientRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (((rawOptimizerDimension n).mul
        (rawOptimizerInteriorSum n (rationalMatrixEntryBitBound A))).div
          (rawOptimizerTau n)) := by
  rw [machineOptimizerInteriorQuotientRawCode,
    machineOptimizerNTimesInteriorSumRawCode_encode,
    machineOptimizerTauRawCode_encode,
    machineRawRatDivCode_encode]

@[simp] theorem machineOptimizerInteriorK0RawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorK0RawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerInteriorK0 n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerInteriorK0RawCode,
    machineOptimizerInteriorQuotientRawCode_encode,
    machineOptimizerNCubeRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerTwiceInteriorK0RawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTwiceInteriorK0RawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerTwiceInteriorK0 n
          (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerTwiceInteriorK0RawCode,
    machineOptimizerInteriorK0RawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem rawOptimizerDimension_value (n : ℕ) :
    (rawOptimizerDimension n).value = n := by
  simp [rawOptimizerDimension]

@[simp] theorem rawOptimizerBitBound_value (B : ℕ) :
    (rawOptimizerBitBound B).value = B := by
  simp [rawOptimizerBitBound]

@[simp] theorem rawOptimizerTau_value (n : ℕ) :
    (rawOptimizerTau n).value = explicitRegularizationScale n := by
  simp [rawOptimizerTau, rawOptimizerXi, rawOptimizerFour,
    rawOptimizerDimension, explicitRegularizationScale]

@[simp] theorem rawOptimizerInteriorK0_value (n B : ℕ) :
    (rawOptimizerInteriorK0 n B).value = numericalInteriorK0 n B
      (explicitRegularizationScale n) := by
  simp [rawOptimizerInteriorK0, rawOptimizerInteriorSum,
    rawOptimizerNSquare, rawOptimizerNCube, numericalInteriorK0,
    rawOptimizerTwo]
  ring

@[simp] theorem rawOptimizerTwiceInteriorK0_value (n B : ℕ) :
    (rawOptimizerTwiceInteriorK0 n B).value =
      2 * numericalInteriorK0 n B (explicitRegularizationScale n) := by
  simp [rawOptimizerTwiceInteriorK0, rawOptimizerTwo]

@[simp] theorem machineOptimizerInteriorExponentBits_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorExponentBits
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      (numericalInteriorExponent n (rationalMatrixEntryBitBound A)
        (explicitRegularizationScale n)).bits := by
  rw [machineOptimizerInteriorExponentBits,
    machineOptimizerTwiceInteriorK0RawCode_encode,
    machineRationalCeilNatBits_encode,
    rawOptimizerTwiceInteriorK0_value]
  rw [numericalInteriorExponent]
  simp [rationalCeilNat, binaryRatCeil_eq_ceil]

/-! ## Guarded unary exponent and dyadic floor -/

def explicitOptimizerInteriorExponentCoefficient : ℕ :=
  34 * rationalCeilNat (8 / explicitXi) + 2

theorem explicitOptimizerInteriorExponentCoefficient_le :
    explicitOptimizerInteriorExponentCoefficient ≤ 17 ^ 60 := by
  norm_num [explicitOptimizerInteriorExponentCoefficient,
    rationalCeilNat, explicitXi, explicitDelta, explicitEta,
    explicitRowRatio]

theorem numericalInteriorExponent_le_sourcePolynomial
    {n B S : ℕ} (hn : 1 ≤ n) (hnS : n ≤ S) (hBS : B ≤ 32 * S) :
    numericalInteriorExponent n B (explicitRegularizationScale n) ≤
      explicitOptimizerInteriorExponentCoefficient * S ^ 4 := by
  have hxi : 0 < explicitXi := explicitXi_pos
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have htau : explicitRegularizationScale n = explicitXi / (4 * n) := rfl
  have hrewrite :
      2 * numericalInteriorK0 n B (explicitRegularizationScale n) =
        (8 / explicitXi) * (n ^ 3 * B + 2 * n ^ 4) + 2 * n ^ 3 := by
    rw [numericalInteriorK0, htau]
    field_simp [hxi.ne', hnQ.ne']
    ring
  let C := rationalCeilNat (8 / explicitXi)
  have hC : (8 / explicitXi : ℚ) ≤ C := by
    exact le_rationalCeilNat (by positivity)
  have hnonneg : (0 : ℚ) ≤ n ^ 3 * B + 2 * n ^ 4 := by positivity
  have hmain :
      (8 / explicitXi : ℚ) * (n ^ 3 * B + 2 * n ^ 4) + 2 * n ^ 3 ≤
        C * (n ^ 3 * B + 2 * n ^ 4) + 2 * n ^ 3 := by
    gcongr
  have hn3 : n ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hn4 : n ^ 4 ≤ S ^ 4 := Nat.pow_le_pow_left hnS 4
  have hS1 : 1 ≤ S := hn.trans hnS
  have hS3S : S ^ 3 ≤ S ^ 4 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hS1
  have hpolyNat :
      C * (n ^ 3 * B + 2 * n ^ 4) + 2 * n ^ 3 ≤
        (34 * C + 2) * S ^ 4 := by
    nlinarith [Nat.mul_le_mul hn3 hBS, hn4, hn3.trans hS3S]
  have hpoly :
      (C : ℚ) * (n ^ 3 * B + 2 * n ^ 4) + 2 * n ^ 3 ≤
        ((34 * C + 2) * S ^ 4 : ℕ) := by
    exact_mod_cast hpolyNat
  apply rationalCeilNat_le_of_le_nat
  rw [hrewrite]
  exact hmain.trans hpoly

def machineOptimizerInteriorExponentGuard (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 6 word

def machineOptimizerInteriorExponentUnary (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerInteriorExponentGuard word)
      (machineOptimizerInteriorExponentBits word))

def machineOptimizerInteriorFloorRawCode (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineOptimizerInteriorExponentUnary word)
      (rawRatBinaryCode rawOptimizerHalf))

def machineExplicitOptimizerFloorRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineOptimizerInteriorFloorRawCode word)
      (rawRatBinaryCode rawOptimizerTwo))

theorem machineOptimizerInteriorExponentGuard_mem_FP :
    machineOptimizerInteriorExponentGuard ∈ FP := by
  simpa only [machineOptimizerInteriorExponentGuard] using!
    machineIteratedBinaryWidth_mem_FP 6

theorem machineOptimizerInteriorExponentUnary_mem_FP :
    machineOptimizerInteriorExponentUnary ∈ FP := by
  simpa only [machineOptimizerInteriorExponentUnary] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerInteriorExponentGuard_mem_FP
      machineOptimizerInteriorExponentBits_mem_FP)
    machineBoundedUnary_mem_FP

theorem machineOptimizerInteriorFloorRawCode_mem_FP :
    machineOptimizerInteriorFloorRawCode ∈ FP := by
  simpa only [machineOptimizerInteriorFloorRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerInteriorExponentUnary_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerHalf)))
    machineRawRatPowerCode_mem_FP

theorem machineExplicitOptimizerFloorRawCode_mem_FP :
    machineExplicitOptimizerFloorRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerFloorRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerInteriorFloorRawCode_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo)))
    machineRawRatDivCode_mem_FP

theorem optimizerInteriorExponent_le_guard {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    numericalInteriorExponent n (rationalMatrixEntryBitBound A)
        (explicitRegularizationScale n) ≤
      (machineOptimizerInteriorExponentGuard
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let S := word.length
  have hnS : n ≤ S := by
    simpa only [S, word] using! matrix_dimension_le_code_length A
  have hBS : rationalMatrixEntryBitBound A ≤ 32 * S := by
    simpa only [S, word] using! rationalMatrixEntryBitBound_le_machineCode hn A
  have hpoly := numericalInteriorExponent_le_sourcePolynomial hn hnS hBS
  have hcoeff :
      explicitOptimizerInteriorExponentCoefficient * S ^ 4 ≤
        (S + 16) ^ 64 := by
    calc
      explicitOptimizerInteriorExponentCoefficient * S ^ 4 ≤
          17 ^ 60 * S ^ 4 :=
        Nat.mul_le_mul explicitOptimizerInteriorExponentCoefficient_le
          (le_refl _)
      _ ≤ (S + 16) ^ 60 * (S + 16) ^ 4 := by
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_left (by omega) 60)
          (Nat.pow_le_pow_left (by omega) 4)
      _ = (S + 16) ^ 64 := by rw [← pow_add]
  calc
    numericalInteriorExponent n (rationalMatrixEntryBitBound A)
        (explicitRegularizationScale n) ≤
        explicitOptimizerInteriorExponentCoefficient * S ^ 4 := hpoly
    _ ≤ (S + 16) ^ 64 := hcoeff
    _ ≤ certificateExpGuardWidth 6 S := by
      simpa using! certificateExpGuardWidth_pow_lower 5 S
    _ = (machineOptimizerInteriorExponentGuard word).length := by
      simp [machineOptimizerInteriorExponentGuard, S]

@[simp] theorem machineOptimizerInteriorExponentUnary_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorExponentUnary
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate
        (numericalInteriorExponent n (rationalMatrixEntryBitBound A)
          (explicitRegularizationScale n)) true := by
  rw [machineOptimizerInteriorExponentUnary,
    machineOptimizerInteriorExponentBits_encode]
  exact machineBoundedUnary_encode_of_le _ _
    (optimizerInteriorExponent_le_guard hn A)

@[simp] theorem rawOptimizerHalf_value : rawOptimizerHalf.value = 1 / 2 := by
  simp [rawOptimizerHalf, rawOptimizerTwo]

@[simp] theorem machineOptimizerInteriorFloorRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInteriorFloorRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerHalf.pow
        (numericalInteriorExponent n (rationalMatrixEntryBitBound A)
          (explicitRegularizationScale n))) := by
  rw [machineOptimizerInteriorFloorRawCode,
    machineOptimizerInteriorExponentUnary_encode hn,
    machineRawRatPowerCode_encode]

@[simp] theorem machineExplicitOptimizerFloorRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerFloorRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode ((rawOptimizerHalf.pow
        (numericalInteriorExponent n (rationalMatrixEntryBitBound A)
          (explicitRegularizationScale n))).div rawOptimizerTwo) := by
  rw [machineExplicitOptimizerFloorRawCode,
    machineOptimizerInteriorFloorRawCode_encode hn,
    machineRawRatDivCode_encode]

theorem machineExplicitOptimizerFloorRawValue {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    ((rawOptimizerHalf.pow
      (numericalInteriorExponent (m + 1) (rationalMatrixEntryBitBound A)
        (explicitRegularizationScale (m + 1)))).div rawOptimizerTwo).value =
      explicitOptimizerFloor A := by
  simp [explicitOptimizerFloor, numericalInteriorFloor,
    rawOptimizerHalf_value, rawOptimizerTwo]

end BeyondBethe
