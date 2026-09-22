/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineCertificatePotentials
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension
import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedLog

/-!
# Dimension-dependent certificate scales as finite-word functions

The directed certificate uses three dimension-dependent quantities: the
regularization scale, the logarithm precision, and the linear KKT and
exponential losses.  This file constructs all of them directly from the
dimension prefix of the optimizer's matrix word.
-/

namespace BeyondBethe

open Complexity

def machineCertificateDimensionBits (word : List Bool) : List Bool :=
  machineMatrixDimensionWord (machineOptimizerMatrixWord word)

def machineCertificateDimensionUnary (word : List Bool) : List Bool :=
  machineMatrixDimensionUnary (machineOptimizerMatrixWord word)

/-- Unary ruler of exact length `n + 400`. -/
def machineCertificateLogPrecisionRuler (word : List Bool) : List Bool :=
  machineCertificateDimensionUnary word ++ List.replicate 400 true

def machineCertificateDimensionRawCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineCertificateDimensionBits word))
    [true]

def rawCertificateFour : RawRat := RawRat.ofNat 4

def machineCertificateFourDimensionRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawCertificateFour)
      (machineCertificateDimensionRawCode word))

def rawExplicitXi : RawRat := rawRatOfRat explicitXi

def machineCertificateRegularizationScaleRawCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode rawExplicitXi)
      (machineCertificateFourDimensionRawCode word))

def rawExplicitKKTError : RawRat := rawRatOfRat explicitKKTError

def machineCertificateKKTPenaltyRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawExplicitKKTError)
      (machineCertificateDimensionRawCode word))

def rawExplicitExpEvaluationLoss : RawRat :=
  rawRatOfRat explicitExpEvaluationLoss

def machineCertificateExpLossRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawExplicitExpEvaluationLoss)
      (machineCertificateDimensionRawCode word))

theorem machineCertificateDimensionBits_mem_FP :
    machineCertificateDimensionBits ∈ Complexity.FP := by
  simpa only [machineCertificateDimensionBits] using!
    machineCompose_mem_FP machineOptimizerMatrixWord_mem_FP
      machineMatrixDimensionWord_mem_FP

theorem machineCertificateDimensionUnary_mem_FP :
    machineCertificateDimensionUnary ∈ Complexity.FP := by
  simpa only [machineCertificateDimensionUnary] using!
    machineCompose_mem_FP machineOptimizerMatrixWord_mem_FP
      machineMatrixDimensionUnary_mem_FP

theorem machineCertificateLogPrecisionRuler_mem_FP :
    machineCertificateLogPrecisionRuler ∈ Complexity.FP := by
  exact machineAppend_mem_FP machineCertificateDimensionUnary_mem_FP
    (machineConst_mem_FP (List.replicate 400 true))

theorem machineCertificateDimensionRawCode_mem_FP :
    machineCertificateDimensionRawCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineCertificateDimensionBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  exact machinePair_mem_FP hnum (machineConst_mem_FP [true])

theorem machineCertificateFourDimensionRawCode_mem_FP :
    machineCertificateFourDimensionRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawCertificateFour))
    machineCertificateDimensionRawCode_mem_FP
  simpa only [machineCertificateFourDimensionRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineCertificateRegularizationScaleRawCode_mem_FP :
    machineCertificateRegularizationScaleRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawExplicitXi))
    machineCertificateFourDimensionRawCode_mem_FP
  simpa only [machineCertificateRegularizationScaleRawCode] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineCertificateKKTPenaltyRawCode_mem_FP :
    machineCertificateKKTPenaltyRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawExplicitKKTError))
    machineCertificateDimensionRawCode_mem_FP
  simpa only [machineCertificateKKTPenaltyRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineCertificateExpLossRawCode_mem_FP :
    machineCertificateExpLossRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP
      (rawRatBinaryCode rawExplicitExpEvaluationLoss))
    machineCertificateDimensionRawCode_mem_FP
  simpa only [machineCertificateExpLossRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

@[simp] theorem machineCertificateDimensionBits_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateDimensionBits
        (rationalOptimizerOutputCode ⟨X, R, C⟩) = n.bits := by
  simp [machineCertificateDimensionBits]

@[simp] theorem machineCertificateDimensionUnary_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateDimensionUnary
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      List.replicate n true := by
  simp [machineCertificateDimensionUnary]

@[simp] theorem machineCertificateLogPrecisionRuler_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateLogPrecisionRuler
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      List.replicate (directedCertificatePrecision n) true := by
  rw [machineCertificateLogPrecisionRuler,
    machineCertificateDimensionUnary_encode]
  change List.replicate n true ++ List.replicate 400 true =
    List.replicate (n + 400) true
  exact (List.replicate_add n 400 true).symm

@[simp] theorem machineCertificateDimensionRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateDimensionRawCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (RawRat.ofNat n) := by
  rw [machineCertificateDimensionRawCode,
    machineCertificateDimensionBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [RawRat.ofNat, rawRatBinaryCode]

def rawCertificateFourDimension (n : ℕ) : RawRat :=
  rawCertificateFour.mul (RawRat.ofNat n)

def rawCertificateRegularizationScale (n : ℕ) : RawRat :=
  rawExplicitXi.div (rawCertificateFourDimension n)

def rawCertificateKKTPenalty (n : ℕ) : RawRat :=
  rawExplicitKKTError.mul (RawRat.ofNat n)

def rawCertificateExpLoss (n : ℕ) : RawRat :=
  rawExplicitExpEvaluationLoss.mul (RawRat.ofNat n)

@[simp] theorem machineCertificateFourDimensionRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateFourDimensionRawCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (rawCertificateFourDimension n) := by
  rw [machineCertificateFourDimensionRawCode,
    machineCertificateDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineCertificateRegularizationScaleRawCode_encode
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ)
    (R C : Fin n → ℚ) :
    machineCertificateRegularizationScaleRawCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (rawCertificateRegularizationScale n) := by
  rw [machineCertificateRegularizationScaleRawCode,
    machineCertificateFourDimensionRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineCertificateKKTPenaltyRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateKKTPenaltyRawCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (rawCertificateKKTPenalty n) := by
  rw [machineCertificateKKTPenaltyRawCode,
    machineCertificateDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineCertificateExpLossRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificateExpLossRawCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (rawCertificateExpLoss n) := by
  rw [machineCertificateExpLossRawCode,
    machineCertificateDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem rawCertificateFour_value : rawCertificateFour.value = 4 := by
  simp [rawCertificateFour]

theorem rawCertificateRegularizationScale_value (n : ℕ) :
    (rawCertificateRegularizationScale n).value =
      explicitRegularizationScale n := by
  simp [rawCertificateRegularizationScale, rawCertificateFourDimension,
    rawExplicitXi, explicitRegularizationScale,
    binaryRatDiv_eq_div, binaryRatMul_eq_mul]

theorem rawCertificateKKTPenalty_value (n : ℕ) :
    (rawCertificateKKTPenalty n).value = explicitKKTError * n := by
  simp [rawCertificateKKTPenalty, rawExplicitKKTError,
    binaryRatMul_eq_mul]

theorem rawCertificateExpLoss_value (n : ℕ) :
    (rawCertificateExpLoss n).value = explicitExpEvaluationLoss * n := by
  simp [rawCertificateExpLoss, rawExplicitExpEvaluationLoss,
    binaryRatMul_eq_mul]

end BeyondBethe
