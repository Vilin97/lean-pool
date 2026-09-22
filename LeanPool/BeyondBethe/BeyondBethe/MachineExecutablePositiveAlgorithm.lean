/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExecutablePositiveRoutine
import LeanPool.BeyondBethe.BeyondBethe.MachineExecutableCertificate
import LeanPool.BeyondBethe.BeyondBethe.MachinePositiveAlgorithm

/-!
# Finite-word realization of the executable positive-matrix routine

This file composes the concrete row-major optimizer, the concrete certificate
evaluator, normalization, and scale restoration.  Correctness is required only
on positive inputs, exactly the domain used by the smoothing reduction.
-/

namespace BeyondBethe

open Complexity

def executableNormalizedCertificateAlgorithm :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 0
  | 1, _ => 0
  | m + 2, B =>
      explicitDirectedCertificateValue
        (executableScannedBetheOptimizerMatrix (m := m + 1) B)
        (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
        (executableScannedBetheOptimizerColumnPotential (m := m + 1) B)

def ExecutableNormalizedCertificateStringRealizesOnPositive
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    F (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩) =
      rawRatBinaryCode
        (rawRatOfRat (executableNormalizedCertificateAlgorithm (m + 2) B))

def machineExecutableNormalizedCertificateRawCode : List Bool → List Bool :=
  machineNormalizedCertificateFromParts
    machineExecutableScannedOptimizerOutputCode
    machineExecutableCertificateValueRawCode

theorem machineExecutableNormalizedCertificateRawCode_mem_FP :
    machineExecutableNormalizedCertificateRawCode ∈ FP := by
  simpa only [machineExecutableNormalizedCertificateRawCode] using!
    machineNormalizedCertificateFromParts_mem_FP
      machineExecutableScannedOptimizerOutputCode_mem_FP
      machineExecutableCertificateValueRawCode_mem_FP

theorem machineExecutableNormalizedCertificateRawCode_realizes_onPositive :
    ExecutableNormalizedCertificateStringRealizesOnPositive
      machineExecutableNormalizedCertificateRawCode := by
  intro m B hBpos hBupper
  rw [machineExecutableNormalizedCertificateRawCode,
    machineNormalizedCertificateFromParts,
    machineCompletedDimensionLtTwoBit_encode,
    show [decide (m + 2 < 2)] = [false] by simp,
    machineIfHead_false,
    machineExecutableScannedOptimizerOutputCode_realizes m B hBpos hBupper,
    machineExecutableCertificateValueRawCode_realizes_onPositive
      m B hBpos hBupper]
  rfl

theorem machineExecutablePositiveLargeRawCode_encode_onPositive
    {certificateMachine : List Bool → List Bool}
    (hrealizes :
      ExecutableNormalizedCertificateStringRealizesOnPositive
        certificateMachine)
    (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hA : Matrix.Positive (fun i j ↦ (A i j : ℝ))) :
    machinePositiveLargeRawCode certificateMachine
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, A⟩) =
      rawRatBinaryCode
        (rawRatOfRat (executablePositiveAlgorithm (m + 2) A)) := by
  have hAq : ∀ i j, 0 < A i j := fun i j ↦ Rat.cast_pos.mp (hA i j)
  have hA0 : Matrix.Nonnegative A := fun i j ↦ (hAq i j).le
  have hBpos : ∀ i j, 0 < normalizedRationalMatrix A i j := by
    intro i j
    rw [normalizedRationalMatrix]
    exact div_pos (hAq i j) (rationalNormalizationScale_pos hA0)
  have hBupper : ∀ i j, normalizedRationalMatrix A i j ≤ 1 :=
    normalizedRationalMatrix_le_one hA0
  have hcertificate := hrealizes m (normalizedRationalMatrix A)
    hBpos hBupper
  change certificateMachine
      (rationalMatrixBinaryEncoding.encode
        ⟨m + 2, normalizedRationalMatrix A⟩) =
    rawRatBinaryCode
      (rawRatOfRat
        (explicitDirectedCertificateValue
          (executableScannedBetheOptimizerMatrix (m := m + 1)
            (normalizedRationalMatrix A))
          (executableScannedBetheOptimizerRowPotential (m := m + 1)
            (normalizedRationalMatrix A))
          (executableScannedBetheOptimizerColumnPotential (m := m + 1)
            (normalizedRationalMatrix A)))) at hcertificate
  simp only [machinePositiveLargeRawCode,
    machinePositiveLargeProductRawCode,
    machinePositiveCertificateRawCode,
    machinePositiveNormalizedMatrixCode,
    machineMatrixNormalizeEntries_encode,
    hcertificate,
    machineMatrixNormalizationScalePowerRawCode_encode,
    machineRawRatMulCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    ← rawRatBinaryCode_rawRatOfRat]
  apply congrArg rawRatBinaryCode
  apply congrArg rawRatOfRat
  rw [binaryNormalizeRawRat_eq_value, RawRat.value_mul,
    RawRat.value_pow, RawRat.value_add, RawRat.value_one,
    rawRatRowsSum_value, RawRat.value_zero, zero_add,
    rationalMatrixRows_sum, rawRatOfRat_value]
  rfl

theorem machinePositiveAlgorithmRawCode_realizes_executable_onPositive
    {certificateMachine : List Bool → List Bool}
    (hrealizes :
      ExecutableNormalizedCertificateStringRealizesOnPositive
        certificateMachine) :
    PositiveRawStringRealizes
      (machinePositiveAlgorithmRawCode certificateMachine)
      executablePositiveAlgorithm := by
  intro n A hA
  rw [machinePositiveAlgorithmRawCode,
    machineCompletedDimensionLtTwoBit_encode]
  by_cases hsmall : n < 2
  · rw [show [decide (n < 2)] = [true] by simp [hsmall],
      machineIfHead_true,
      machinePositiveSmallRawCode_encode hsmall]
    interval_cases n <;> rfl
  · rw [show [decide (n < 2)] = [false] by simp [hsmall],
      machineIfHead_false]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      use n - 2
      omega
    exact machineExecutablePositiveLargeRawCode_encode_onPositive
      hrealizes m A hA

def machineExecutablePositiveAlgorithmRawCode : List Bool → List Bool :=
  machinePositiveAlgorithmRawCode
    machineExecutableNormalizedCertificateRawCode

theorem machineExecutablePositiveAlgorithmRawCode_mem_FP :
    machineExecutablePositiveAlgorithmRawCode ∈ FP := by
  simpa only [machineExecutablePositiveAlgorithmRawCode] using!
    machinePositiveAlgorithmRawCode_mem_FP
      machineExecutableNormalizedCertificateRawCode_mem_FP

theorem machineExecutablePositiveAlgorithmRawCode_realizes_onPositive :
    PositiveRawStringRealizes
      machineExecutablePositiveAlgorithmRawCode
      executablePositiveAlgorithm := by
  simpa only [machineExecutablePositiveAlgorithmRawCode] using!
    machinePositiveAlgorithmRawCode_realizes_executable_onPositive
      machineExecutableNormalizedCertificateRawCode_realizes_onPositive

end BeyondBethe
