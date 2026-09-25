/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineFinalScalars
public import LeanPool.BeyondBethe.BeyondBethe.MachinePerfectMatching
public import LeanPool.BeyondBethe.BeyondBethe.MachineSmoothedMatrix
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitScales

/-!
# Finite-word outer wrapper for the completed permanent algorithm

This module closes every branch and final scalar operation in
`completedAlgorithm`. It is parameterized by one internal machine for the
positive-matrix routine. That internal machine returns an unreduced rational
word, allowing the verified rational arithmetic layer to consume its result.
The executable development later supplies this parameter with the concrete
regularized-Bethe optimizer and certificate machine.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Internal realization relation for a rational-matrix algorithm whose
machine output is a raw numerator/denominator pair rather than the public
one-natural rational encoding. -/
def RawStringRealizes
    (F : List Bool → List Bool)
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ) : Prop :=
  ∀ x : RationalMatrixInput,
    F (rationalMatrixBinaryEncoding.encode x) =
      rawRatBinaryCode (rawRatOfRat (bundledAlgorithm alg x))

/-- Correctness relation needed of an internal positive-matrix routine.  The
outer smoothing wrapper calls it only on strictly positive matrices, so no
semantic requirement is imposed on its totalized behavior elsewhere. -/
def PositiveRawStringRealizes
    (F : List Bool → List Bool)
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    Matrix.Positive (fun i j ↦ (A i j : ℝ)) →
    F (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawRatOfRat (alg n A))

/-- Tests whether the encoded matrix dimension is less than two. -/
def machineCompletedDimensionLtTwoBit (word : List Bool) : List Bool :=
  machineBinaryNatLtBit
    (pair (machineMatrixDimensionWord word) (2 : ℕ).bits)

/-- Encodes the matrix obtained by smoothing the input with rational parameter `χ`. -/
def machineCompletedSmoothedMatrixCode (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineSmoothedMatrixCode
    (pair (rawRatBinaryCode (rawRatOfRat χ)) word)

/-- Runs the supplied positive-input machine on the encoded smoothed matrix. -/
def machineCompletedPositiveRawCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  positiveMachine (machineCompletedSmoothedMatrixCode χ word)

/-- Obtains the raw-rational dimension code through the smoothing input format. -/
def machineCompletedDimensionRawCode (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineSmoothingDimensionRawCode
    (pair (rawRatBinaryCode (rawRatOfRat χ)) word)

/-- Computes the encoded product of `χ` and the matrix dimension. -/
def machineCompletedChiTimesDimensionRawCode (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode (rawRatOfRat χ))
      (machineCompletedDimensionRawCode χ word))

/-- Computes the encoded smoothing correction term `χ * n / 2`. -/
def machineCompletedHalfChiDimensionRawCode (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineCompletedChiTimesDimensionRawCode χ word)
      (rawRatBinaryCode (RawRat.ofNat 2)))

/-- Computes the encoded denominator correction `1 + χ * n / 2`. -/
def machineCompletedCorrectionRawCode (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineCompletedHalfChiDimensionRawCode χ word))

/-- Multiplies the positive-machine output by the matrix normalization scale raised to its
dimension. -/
def machineCompletedLargeNumeratorRawCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineMatrixNormalizationScalePowerRawCode word)
      (machineCompletedPositiveRawCode positiveMachine χ word))

/-- Divides the scaled positive-machine output by the smoothing correction `1 + χ * n / 2`. -/
def machineCompletedLargeRawCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineCompletedLargeNumeratorRawCode positiveMachine χ word)
      (machineCompletedCorrectionRawCode χ word))

/-- Normalizes the raw-rational result of the large-dimension branch. -/
def machineCompletedLargeCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode
    (machineCompletedLargeRawCode positiveMachine χ word)

/-- Runs the corrected positive branch when the support has a perfect matching, returning zero
otherwise. -/
def machineCompletedMatchingBranchCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineIfHead (machineKuhnPerfectMatchingBit word)
    (machineCompletedLargeCode positiveMachine χ word)
    (rationalBinaryCode 0)

/-- Handles dimensions below two directly and otherwise dispatches to the perfect-matching
branch. -/
def machineCompletedNonnegativeBranchCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineIfHead (machineCompletedDimensionLtTwoBit word)
    (machineSmallDimensionPermanentCode word)
    (machineCompletedMatchingBranchCode positiveMachine χ word)

/-- Dispatches nonnegative matrices to the completed algorithm and returns zero for a failed
sign test. -/
def machineCompletedAlgorithmCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineIfHead (machineMatrixNonnegativeBit word)
    (machineCompletedNonnegativeBranchCode positiveMachine χ word)
    (rationalBinaryCode 0)

theorem machineCompletedDimensionLtTwoBit_mem_FP :
    machineCompletedDimensionLtTwoBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixDimensionWord_mem_FP
    (machineConst_mem_FP (2 : ℕ).bits)
  simpa only [machineCompletedDimensionLtTwoBit] using!
    machineCompose_mem_FP hpair machineBinaryNatLtBit_mem_FP

theorem machineCompletedSmoothedMatrixCode_mem_FP (χ : ℚ) :
    machineCompletedSmoothedMatrixCode χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (rawRatOfRat χ))) id_mem_FP
  simpa only [machineCompletedSmoothedMatrixCode] using!
    machineCompose_mem_FP hpair machineSmoothedMatrixCode_mem_FP

theorem machineCompletedPositiveRawCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedPositiveRawCode positiveMachine χ ∈ Complexity.FP := by
  simpa only [machineCompletedPositiveRawCode] using!
    machineCompose_mem_FP (machineCompletedSmoothedMatrixCode_mem_FP χ)
      hpositive

theorem machineCompletedDimensionRawCode_mem_FP (χ : ℚ) :
    machineCompletedDimensionRawCode χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (rawRatOfRat χ))) id_mem_FP
  simpa only [machineCompletedDimensionRawCode] using!
    machineCompose_mem_FP hpair machineSmoothingDimensionRawCode_mem_FP

theorem machineCompletedChiTimesDimensionRawCode_mem_FP (χ : ℚ) :
    machineCompletedChiTimesDimensionRawCode χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (rawRatOfRat χ)))
    (machineCompletedDimensionRawCode_mem_FP χ)
  simpa only [machineCompletedChiTimesDimensionRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineCompletedHalfChiDimensionRawCode_mem_FP (χ : ℚ) :
    machineCompletedHalfChiDimensionRawCode χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineCompletedChiTimesDimensionRawCode_mem_FP χ)
    (machineConst_mem_FP (rawRatBinaryCode (RawRat.ofNat 2)))
  simpa only [machineCompletedHalfChiDimensionRawCode] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineCompletedCorrectionRawCode_mem_FP (χ : ℚ) :
    machineCompletedCorrectionRawCode χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    (machineCompletedHalfChiDimensionRawCode_mem_FP χ)
  simpa only [machineCompletedCorrectionRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineCompletedLargeNumeratorRawCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedLargeNumeratorRawCode positiveMachine χ ∈
      Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineMatrixNormalizationScalePowerRawCode_mem_FP
    (machineCompletedPositiveRawCode_mem_FP hpositive χ)
  simpa only [machineCompletedLargeNumeratorRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineCompletedLargeRawCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedLargeRawCode positiveMachine χ ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineCompletedLargeNumeratorRawCode_mem_FP hpositive χ)
    (machineCompletedCorrectionRawCode_mem_FP χ)
  simpa only [machineCompletedLargeRawCode] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineCompletedLargeCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedLargeCode positiveMachine χ ∈ Complexity.FP := by
  simpa only [machineCompletedLargeCode] using!
    machineCompose_mem_FP
      (machineCompletedLargeRawCode_mem_FP hpositive χ)
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineCompletedMatchingBranchCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedMatchingBranchCode positiveMachine χ ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineKuhnPerfectMatchingBit_mem_FP
    (machineCompletedLargeCode_mem_FP hpositive χ)
    (machineConst_mem_FP (rationalBinaryCode 0))

theorem machineCompletedNonnegativeBranchCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedNonnegativeBranchCode positiveMachine χ ∈
      Complexity.FP := by
  exact machineIfHead_mem_FP machineCompletedDimensionLtTwoBit_mem_FP
    machineSmallDimensionPermanentCode_mem_FP
    (machineCompletedMatchingBranchCode_mem_FP hpositive χ)

theorem machineCompletedAlgorithmCode_mem_FP
    {positiveMachine : List Bool → List Bool}
    (hpositive : positiveMachine ∈ Complexity.FP) (χ : ℚ) :
    machineCompletedAlgorithmCode positiveMachine χ ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineMatrixNonnegativeBit_mem_FP
    (machineCompletedNonnegativeBranchCode_mem_FP hpositive χ)
    (machineConst_mem_FP (rationalBinaryCode 0))

/-! ## Exact semantics -/

@[simp] theorem machineCompletedDimensionLtTwoBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineCompletedDimensionLtTwoBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [decide (n < 2)] := by
  rw [machineCompletedDimensionLtTwoBit,
    machineMatrixDimensionWord_encode,
    machineBinaryNatLtBit_pair_natBits]

@[simp] theorem machineCompletedCorrectionRawCode_encode {n : ℕ}
    (χ : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineCompletedCorrectionRawCode χ
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (RawRat.one.add
          (((rawRatOfRat χ).mul (RawRat.ofNat n)).div
            (RawRat.ofNat 2))) := by
  simp only [machineCompletedCorrectionRawCode,
    machineCompletedHalfChiDimensionRawCode,
    machineCompletedChiTimesDimensionRawCode,
    machineCompletedDimensionRawCode]
  rw [machineSmoothingDimensionRawCode_encode A (rawRatOfRat χ),
    machineRawRatMulCode_encode, machineRawRatDivCode_encode,
    machineRawRatAddCode_encode]

theorem machineKuhnPerfectMatchingBit_finalDecision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineKuhnPerfectMatchingBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [kuhnSupportMatchingDecision A] := by
  rw [machineKuhnPerfectMatchingBit_encode]
  apply congrArg singleton
  apply Bool.eq_iff_iff.mpr
  rw [kuhnColumnMate_all_isSome_eq_true_iff,
    kuhnSupportMatchingDecision_eq_true_iff]

theorem machineCompletedLargeCode_encode
    {positiveMachine : List Bool → List Bool}
    {positiveAlg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ}
    (hrealizes : RawStringRealizes positiveMachine positiveAlg)
    (χ : ℚ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineCompletedLargeCode positiveMachine χ
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode
        (rationalNormalizationScale A ^ n *
            positiveAlg n (smoothedRationalMatrix A χ) /
          (1 + χ * n / 2)) := by
  have hpositive := hrealizes
    ⟨n, smoothedRationalMatrix A χ⟩
  change positiveMachine
      (rationalMatrixBinaryEncoding.encode
        ⟨n, smoothedRationalMatrix A χ⟩) =
    rawRatBinaryCode
      (rawRatOfRat (positiveAlg n (smoothedRationalMatrix A χ))) at hpositive
  simp only [machineCompletedLargeCode,
    machineCompletedLargeRawCode,
    machineCompletedLargeNumeratorRawCode,
    machineCompletedPositiveRawCode,
    machineCompletedSmoothedMatrixCode,
    machineSmoothedMatrixCode_rational,
    hpositive,
    machineMatrixNormalizationScalePowerRawCode_encode,
    machineCompletedCorrectionRawCode_encode,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_div, RawRat.value_pow,
    RawRat.value_mul, RawRat.value_add, RawRat.value_one,
    RawRat.value_ofNat, rawRatOfRat_value,
    rawRatRowsSum_value, RawRat.value_zero, zero_add,
    rationalMatrixRows_sum, rationalNormalizationScale]
  congr 1

/-- The large branch only invokes the internal routine on the strictly
positive smoothed matrix.  This version records precisely that domain instead
of requiring arbitrary behavior from the internal machine away from it. -/
theorem machineCompletedLargeCode_encode_onPositive
    {positiveMachine : List Bool → List Bool}
    {positiveAlg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ}
    (hrealizes : PositiveRawStringRealizes positiveMachine positiveAlg)
    (χ : ℚ) (hχ : 0 < (χ : ℝ)) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : Matrix.Nonnegative A) :
    machineCompletedLargeCode positiveMachine χ
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode
        (rationalNormalizationScale A ^ n *
            positiveAlg n (smoothedRationalMatrix A χ) /
          (1 + χ * n / 2)) := by
  have hpositive := hrealizes n (smoothedRationalMatrix A χ)
    (cast_smoothedRationalMatrix_positive hn A hA χ hχ)
  simp only [machineCompletedLargeCode,
    machineCompletedLargeRawCode,
    machineCompletedLargeNumeratorRawCode,
    machineCompletedPositiveRawCode,
    machineCompletedSmoothedMatrixCode,
    machineSmoothedMatrixCode_rational,
    hpositive,
    machineMatrixNormalizationScalePowerRawCode_encode,
    machineCompletedCorrectionRawCode_encode,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_div, RawRat.value_pow,
    RawRat.value_mul, RawRat.value_add, RawRat.value_one,
    RawRat.value_ofNat, rawRatOfRat_value,
    rawRatRowsSum_value, RawRat.value_zero, zero_add,
    rationalMatrixRows_sum, rationalNormalizationScale]
  congr 1

theorem machineCompletedAlgorithmCode_encode
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε)
    {positiveMachine : List Bool → List Bool}
    (hrealizes : RawStringRealizes positiveMachine routine.alg)
    (χ : ℚ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineCompletedAlgorithmCode positiveMachine χ
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (completedAlgorithm routine χ n A) := by
  rw [machineCompletedAlgorithmCode,
    machineMatrixNonnegativeBit_finalDecision]
  by_cases hnonnegative : rationalMatrixNonnegativeDecision A = true
  · rw [show [rationalMatrixNonnegativeDecision A] = [true] by simp [hnonnegative],
      machineIfHead_true]
    rw [machineCompletedNonnegativeBranchCode,
      machineCompletedDimensionLtTwoBit_encode]
    by_cases hsmall : n < 2
    · rw [show [decide (n < 2)] = [true] by simp [hsmall],
        machineIfHead_true,
        machineSmallDimensionPermanentCode_encode hsmall]
      simp [completedAlgorithm, hnonnegative, hsmall]
    · rw [show [decide (n < 2)] = [false] by simp [hsmall],
        machineIfHead_false,
        machineCompletedMatchingBranchCode,
        machineKuhnPerfectMatchingBit_finalDecision]
      by_cases hmatching : kuhnSupportMatchingDecision A = true
      · rw [show [kuhnSupportMatchingDecision A] = [true] by simp [hmatching],
          machineIfHead_true,
          machineCompletedLargeCode_encode hrealizes]
        simp [completedAlgorithm, hnonnegative, hsmall, hmatching]
      · rw [show [kuhnSupportMatchingDecision A] = [false] by
            simp [Bool.eq_false_iff.mpr hmatching],
          machineIfHead_false]
        simp [completedAlgorithm, hnonnegative, hsmall, hmatching]
  · rw [show [rationalMatrixNonnegativeDecision A] = [false] by
        simp [Bool.eq_false_iff.mpr hnonnegative],
      machineIfHead_false]
    simp [completedAlgorithm, hnonnegative]

/-- Exact semantics of the total outer machine from correctness of its
internal routine only on positive matrices.  Positivity is discharged by the
verified smoothing step at the unique call site. -/
theorem machineCompletedAlgorithmCode_encode_onPositive
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε)
    {positiveMachine : List Bool → List Bool}
    (hrealizes : PositiveRawStringRealizes positiveMachine routine.alg)
    (χ : ℚ) (hχ : 0 < (χ : ℝ)) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineCompletedAlgorithmCode positiveMachine χ
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (completedAlgorithm routine χ n A) := by
  rw [machineCompletedAlgorithmCode,
    machineMatrixNonnegativeBit_finalDecision]
  by_cases hnonnegative : rationalMatrixNonnegativeDecision A = true
  · have hA : Matrix.Nonnegative A :=
      (rationalMatrixNonnegativeDecision_eq_true_iff A).1 hnonnegative
    rw [show [rationalMatrixNonnegativeDecision A] = [true] by simp [hnonnegative],
      machineIfHead_true]
    rw [machineCompletedNonnegativeBranchCode,
      machineCompletedDimensionLtTwoBit_encode]
    by_cases hsmall : n < 2
    · rw [show [decide (n < 2)] = [true] by simp [hsmall],
        machineIfHead_true,
        machineSmallDimensionPermanentCode_encode hsmall]
      simp [completedAlgorithm, hnonnegative, hsmall]
    · have hn : 0 < n := by omega
      rw [show [decide (n < 2)] = [false] by simp [hsmall],
        machineIfHead_false,
        machineCompletedMatchingBranchCode,
        machineKuhnPerfectMatchingBit_finalDecision]
      by_cases hmatching : kuhnSupportMatchingDecision A = true
      · rw [show [kuhnSupportMatchingDecision A] = [true] by simp [hmatching],
          machineIfHead_true,
          machineCompletedLargeCode_encode_onPositive hrealizes χ hχ hn A hA]
        simp [completedAlgorithm, hnonnegative, hsmall, hmatching]
      · rw [show [kuhnSupportMatchingDecision A] = [false] by
            simp [Bool.eq_false_iff.mpr hmatching],
          machineIfHead_false]
        simp [completedAlgorithm, hnonnegative, hsmall, hmatching]
  · rw [show [rationalMatrixNonnegativeDecision A] = [false] by
        simp [Bool.eq_false_iff.mpr hnonnegative],
      machineIfHead_false]
    simp [completedAlgorithm, hnonnegative]

theorem completedAlgorithm_runsInPolynomialTime_of_rawMachine
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε)
    {positiveMachine : List Bool → List Bool}
    (hpositiveFP : positiveMachine ∈ Complexity.FP)
    (hrealizes : RawStringRealizes positiveMachine routine.alg)
    (χ : ℚ) :
    RunsInPolynomialTime (completedAlgorithm routine χ) := by
  refine ⟨machineCompletedAlgorithmCode positiveMachine χ,
    machineCompletedAlgorithmCode_mem_FP hpositiveFP χ, ?_⟩
  intro x
  obtain ⟨n, A⟩ := x
  exact machineCompletedAlgorithmCode_encode routine hrealizes χ A

/-- Polynomial time of the completed algorithm from a total polynomial-time
internal machine whose semantic contract is restricted to positive inputs. -/
theorem completedAlgorithm_runsInPolynomialTime_of_positive_rawMachine
    {ε : ℝ} (routine : CertifiedPositiveRoutine ε)
    {positiveMachine : List Bool → List Bool}
    (hpositiveFP : positiveMachine ∈ Complexity.FP)
    (hrealizes : PositiveRawStringRealizes positiveMachine routine.alg)
    (χ : ℚ) (hχ : 0 < (χ : ℝ)) :
    RunsInPolynomialTime (completedAlgorithm routine χ) := by
  refine ⟨machineCompletedAlgorithmCode positiveMachine χ,
    machineCompletedAlgorithmCode_mem_FP hpositiveFP χ, ?_⟩
  intro x
  obtain ⟨n, A⟩ := x
  exact machineCompletedAlgorithmCode_encode_onPositive
    routine hrealizes χ hχ A

end BeyondBethe
