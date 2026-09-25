/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineCompletedAlgorithm
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitPositiveRoutine

/-!
# Finite-word wrapper for the positive-matrix routine

This module removes normalization, scale restoration, and the exact small
dimensions from the remaining positive-routine boundary.  The only parameter
is a raw-output machine for the normalized optimizer-plus-certificate value.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Returns zero in dimensions zero and one; otherwise evaluates the directed certificate at the
explicit optimizer matrix and its row and column potentials. -/
def explicitNormalizedCertificateAlgorithm :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 0
  | 1, _ => 0
  | m + 2, B =>
      explicitDirectedCertificateValue
        (explicitBetheOptimizerMatrix (m := m + 1) B)
        (explicitBetheOptimizerRowPotential (m := m + 1) B)
        (explicitBetheOptimizerColumnPotential (m := m + 1) B)

/-- Conditional realization of the normalized optimizer-certificate value on
the positive, entrywise-at-most-one matrices supplied by normalization. -/
def NormalizedCertificateStringRealizesOnPositive
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    F (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩) =
      rawRatBinaryCode
        (rawRatOfRat (explicitNormalizedCertificateAlgorithm (m + 2) B))

/-- Returns raw one for a zero-dimensional positive-matrix input and its first entry otherwise. -/
def machinePositiveSmallRawCode (word : List Bool) : List Bool :=
  machineIfHead (machineMatrixDimensionZeroBit word)
    (rawRatBinaryCode RawRat.one)
    (machineMatrixFirstEntryCode word)

/-- Normalizes the positive input matrix's entries for the certificate machine. -/
def machinePositiveNormalizedMatrixCode (word : List Bool) : List Bool :=
  machineMatrixNormalizeEntries word

/-- Runs the supplied certificate machine on the normalized positive matrix. -/
def machinePositiveCertificateRawCode
    (certificateMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  certificateMachine (machinePositiveNormalizedMatrixCode word)

/-- Multiplies the normalized-matrix certificate by the matrix-normalization scale raised to the
dimension. -/
def machinePositiveLargeProductRawCode
    (certificateMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineMatrixNormalizationScalePowerRawCode word)
      (machinePositiveCertificateRawCode certificateMachine word))

/-- Normalizes the scaled certificate product into a rational entry code. -/
def machinePositiveLargeRawCode
    (certificateMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machinePositiveLargeProductRawCode certificateMachine word)

/-- Uses the direct small-dimension branch below dimension two and the scaled
normalized-certificate branch otherwise. -/
def machinePositiveAlgorithmRawCode
    (certificateMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineIfHead (machineCompletedDimensionLtTwoBit word)
    (machinePositiveSmallRawCode word)
    (machinePositiveLargeRawCode certificateMachine word)

theorem machinePositiveSmallRawCode_mem_FP :
    machinePositiveSmallRawCode ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineMatrixDimensionZeroBit_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineMatrixFirstEntryCode_mem_FP

theorem machinePositiveNormalizedMatrixCode_mem_FP :
    machinePositiveNormalizedMatrixCode ∈ Complexity.FP :=
  machineMatrixNormalizeEntries_mem_FP

theorem machinePositiveCertificateRawCode_mem_FP
    {certificateMachine : List Bool → List Bool}
    (hcertificate : certificateMachine ∈ Complexity.FP) :
    machinePositiveCertificateRawCode certificateMachine ∈ Complexity.FP := by
  simpa only [machinePositiveCertificateRawCode] using!
    machineCompose_mem_FP machinePositiveNormalizedMatrixCode_mem_FP
      hcertificate

theorem machinePositiveLargeProductRawCode_mem_FP
    {certificateMachine : List Bool → List Bool}
    (hcertificate : certificateMachine ∈ Complexity.FP) :
    machinePositiveLargeProductRawCode certificateMachine ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineMatrixNormalizationScalePowerRawCode_mem_FP
    (machinePositiveCertificateRawCode_mem_FP hcertificate)
  simpa only [machinePositiveLargeProductRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machinePositiveLargeRawCode_mem_FP
    {certificateMachine : List Bool → List Bool}
    (hcertificate : certificateMachine ∈ Complexity.FP) :
    machinePositiveLargeRawCode certificateMachine ∈ Complexity.FP := by
  simpa only [machinePositiveLargeRawCode] using!
    machineCompose_mem_FP
      (machinePositiveLargeProductRawCode_mem_FP hcertificate)
      machineNormalizeRawRatEntryCode_mem_FP

theorem machinePositiveAlgorithmRawCode_mem_FP
    {certificateMachine : List Bool → List Bool}
    (hcertificate : certificateMachine ∈ Complexity.FP) :
    machinePositiveAlgorithmRawCode certificateMachine ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineCompletedDimensionLtTwoBit_mem_FP
    machinePositiveSmallRawCode_mem_FP
    (machinePositiveLargeRawCode_mem_FP hcertificate)

@[simp] theorem machinePositiveSmallRawCode_zero
    (A : Matrix (Fin 0) (Fin 0) ℚ) :
    machinePositiveSmallRawCode
        (rationalMatrixBinaryEncoding.encode ⟨0, A⟩) =
      rawRatBinaryCode (rawRatOfRat (Matrix.permanent A)) := by
  simp [machinePositiveSmallRawCode, Matrix.permanent,
    rawRatBinaryCode, rawRatOfRat, integerBinaryCode, RawRat.one]

@[simp] theorem machinePositiveSmallRawCode_one
    (A : Matrix (Fin 1) (Fin 1) ℚ) :
    machinePositiveSmallRawCode
        (rationalMatrixBinaryEncoding.encode ⟨1, A⟩) =
      rawRatBinaryCode (rawRatOfRat (Matrix.permanent A)) := by
  simp [machinePositiveSmallRawCode, Matrix.permanent_fin_one,
    rawRatBinaryCode_rawRatOfRat]

theorem machinePositiveSmallRawCode_encode {n : ℕ}
    (hn : n < 2) (A : Matrix (Fin n) (Fin n) ℚ) :
    machinePositiveSmallRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawRatOfRat (Matrix.permanent A)) := by
  interval_cases n
  · exact machinePositiveSmallRawCode_zero A
  · exact machinePositiveSmallRawCode_one A

theorem machinePositiveLargeRawCode_encode
    {certificateMachine : List Bool → List Bool}
    (hrealizes : RawStringRealizes certificateMachine
      explicitNormalizedCertificateAlgorithm)
    (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ) :
    machinePositiveLargeRawCode certificateMachine
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, A⟩) =
      rawRatBinaryCode
        (rawRatOfRat (explicitPositiveAlgorithm (m + 2) A)) := by
  have hcertificate := hrealizes
    ⟨m + 2, normalizedRationalMatrix A⟩
  change certificateMachine
      (rationalMatrixBinaryEncoding.encode
        ⟨m + 2, normalizedRationalMatrix A⟩) =
    rawRatBinaryCode
      (rawRatOfRat
        (explicitDirectedCertificateValue
          (explicitBetheOptimizerMatrix (m := m + 1)
            (normalizedRationalMatrix A))
          (explicitBetheOptimizerRowPotential (m := m + 1)
            (normalizedRationalMatrix A))
          (explicitBetheOptimizerColumnPotential (m := m + 1)
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

theorem machinePositiveLargeRawCode_encode_onPositive
    {certificateMachine : List Bool → List Bool}
    (hrealizes :
      NormalizedCertificateStringRealizesOnPositive certificateMachine)
    (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hA : Matrix.Positive (fun i j ↦ (A i j : ℝ))) :
    machinePositiveLargeRawCode certificateMachine
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, A⟩) =
      rawRatBinaryCode
        (rawRatOfRat (explicitPositiveAlgorithm (m + 2) A)) := by
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
          (explicitBetheOptimizerMatrix (m := m + 1)
            (normalizedRationalMatrix A))
          (explicitBetheOptimizerRowPotential (m := m + 1)
            (normalizedRationalMatrix A))
          (explicitBetheOptimizerColumnPotential (m := m + 1)
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

theorem machinePositiveAlgorithmRawCode_realizes
    {certificateMachine : List Bool → List Bool}
    (hrealizes : RawStringRealizes certificateMachine
      explicitNormalizedCertificateAlgorithm) :
    RawStringRealizes
      (machinePositiveAlgorithmRawCode certificateMachine)
      explicitPositiveAlgorithm := by
  intro x
  obtain ⟨n, A⟩ := x
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
    exact machinePositiveLargeRawCode_encode hrealizes m A

theorem machinePositiveAlgorithmRawCode_realizes_onPositive
    {certificateMachine : List Bool → List Bool}
    (hrealizes :
      NormalizedCertificateStringRealizesOnPositive certificateMachine) :
    PositiveRawStringRealizes
      (machinePositiveAlgorithmRawCode certificateMachine)
      explicitPositiveAlgorithm := by
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
    exact machinePositiveLargeRawCode_encode_onPositive hrealizes m A hA

theorem explicitPositiveAlgorithm_rawMachine_of_certificateMachine
    {certificateMachine : List Bool → List Bool}
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hrealizes : RawStringRealizes certificateMachine
      explicitNormalizedCertificateAlgorithm) :
    ∃ positiveMachine : List Bool → List Bool,
      positiveMachine ∈ Complexity.FP ∧
      RawStringRealizes positiveMachine explicitPositiveAlgorithm := by
  exact ⟨machinePositiveAlgorithmRawCode certificateMachine,
    machinePositiveAlgorithmRawCode_mem_FP hcertificateFP,
    machinePositiveAlgorithmRawCode_realizes hrealizes⟩

theorem explicitPositiveAlgorithm_positive_rawMachine_of_certificateMachine
    {certificateMachine : List Bool → List Bool}
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hrealizes :
      NormalizedCertificateStringRealizesOnPositive certificateMachine) :
    ∃ positiveMachine : List Bool → List Bool,
      positiveMachine ∈ Complexity.FP ∧
      PositiveRawStringRealizes positiveMachine explicitPositiveAlgorithm := by
  exact ⟨machinePositiveAlgorithmRawCode certificateMachine,
    machinePositiveAlgorithmRawCode_mem_FP hcertificateFP,
    machinePositiveAlgorithmRawCode_realizes_onPositive hrealizes⟩

end BeyondBethe
