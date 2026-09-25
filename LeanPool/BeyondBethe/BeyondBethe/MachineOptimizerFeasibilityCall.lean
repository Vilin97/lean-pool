/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerStateBound
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalBallInit

/-!
# A complete finite-word Bethe threshold call

This module assembles one canonical threshold-feasibility input directly from
the matrix word and a raw rational threshold.  Every numerical parameter,
the initial ball, and the state-size ruler are produced by verified
finite-word machines.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineOptimizerFeasibilityReducedDimensionUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerFeasibilitySource word)
      (machineOptimizerFeasibilityReducedDimensionBits word))

def machineOptimizerFeasibilityTauCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerTauRawCode (machineOptimizerFeasibilitySource word))

def machineOptimizerFeasibilityDeltaRawCode
    (word : List Bool) : List Bool :=
  machineExplicitOptimizerFloorRawCode
    (machineOptimizerFeasibilitySource word)

def machineOptimizerFeasibilityOracleStaticCode
    (word : List Bool) : List Bool :=
  pair (machineOptimizerFeasibilityReducedDimensionUnary word)
    (pair
      (machineExplicitOptimizerPrecisionRuler
        (machineOptimizerFeasibilitySource word))
      (pair (machineOptimizerFeasibilityTauCode word)
        (pair (machineOptimizerFeasibilityDeltaRawCode word)
          (pair (machineOptimizerFeasibilityUpperRawCode word)
            (machineOptimizerFeasibilitySource word)))))

def machineOptimizerFeasibilityInitialBallCode
    (word : List Bool) : List Bool :=
  machineRationalBallStateCode
    (pair (machineOptimizerFeasibilityEllipsoidDimensionUnary word)
      (machineOptimizerFeasibilityOuterRadiusEntryCode word))

def machineOptimizerFeasibilityLoopWord
    (word : List Bool) : List Bool :=
  pair (machineOptimizerFeasibilityBudgetUnary word)
    (pair (machineOptimizerFeasibilityStateBoundUnary word)
      (pair (machineOptimizerFeasibilityRoundingPrecisionUnary word)
        (pair (machineOptimizerFeasibilityOracleStaticCode word)
          (machineOptimizerFeasibilityInitialBallCode word))))

def machineExplicitBetheThresholdFeasibilityCode
    (word : List Bool) : List Bool :=
  machineBetheFeasibilityResultCode
    (machineOptimizerFeasibilityLoopWord word)

/-! ## Polynomial-time closure -/

theorem machineOptimizerFeasibilityReducedDimensionUnary_mem_FP :
    machineOptimizerFeasibilityReducedDimensionUnary ∈ FP := by
  simpa only [machineOptimizerFeasibilityReducedDimensionUnary] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilitySource_mem_FP
        machineOptimizerFeasibilityReducedDimensionBits_mem_FP)
      machineBoundedUnary_mem_FP

theorem machineOptimizerFeasibilityTauCode_mem_FP :
    machineOptimizerFeasibilityTauCode ∈ FP := by
  have htau := machineCompose_mem_FP
    machineOptimizerFeasibilitySource_mem_FP
    machineOptimizerTauRawCode_mem_FP
  simpa only [machineOptimizerFeasibilityTauCode] using!
    machineCompose_mem_FP htau machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerFeasibilityDeltaRawCode_mem_FP :
    machineOptimizerFeasibilityDeltaRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityDeltaRawCode] using!
    machineCompose_mem_FP machineOptimizerFeasibilitySource_mem_FP
      machineExplicitOptimizerFloorRawCode_mem_FP

theorem machineOptimizerFeasibilityOracleStaticCode_mem_FP :
    machineOptimizerFeasibilityOracleStaticCode ∈ FP := by
  exact machinePair_mem_FP
    machineOptimizerFeasibilityReducedDimensionUnary_mem_FP
    (machinePair_mem_FP
      (machineCompose_mem_FP machineOptimizerFeasibilitySource_mem_FP
        machineExplicitOptimizerPrecisionRuler_mem_FP)
      (machinePair_mem_FP machineOptimizerFeasibilityTauCode_mem_FP
        (machinePair_mem_FP
          machineOptimizerFeasibilityDeltaRawCode_mem_FP
          (machinePair_mem_FP
            machineOptimizerFeasibilityUpperRawCode_mem_FP
            machineOptimizerFeasibilitySource_mem_FP))))

theorem machineOptimizerFeasibilityInitialBallCode_mem_FP :
    machineOptimizerFeasibilityInitialBallCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityInitialBallCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityEllipsoidDimensionUnary_mem_FP
        machineOptimizerFeasibilityOuterRadiusEntryCode_mem_FP)
      machineRationalBallStateCode_mem_FP

theorem machineOptimizerFeasibilityLoopWord_mem_FP :
    machineOptimizerFeasibilityLoopWord ∈ FP := by
  exact machinePair_mem_FP machineOptimizerFeasibilityBudgetUnary_mem_FP
    (machinePair_mem_FP machineOptimizerFeasibilityStateBoundUnary_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityRoundingPrecisionUnary_mem_FP
        (machinePair_mem_FP
          machineOptimizerFeasibilityOracleStaticCode_mem_FP
          machineOptimizerFeasibilityInitialBallCode_mem_FP)))

theorem machineExplicitBetheThresholdFeasibilityCode_mem_FP :
    machineExplicitBetheThresholdFeasibilityCode ∈ FP := by
  simpa only [machineExplicitBetheThresholdFeasibilityCode] using!
    machineCompose_mem_FP machineOptimizerFeasibilityLoopWord_mem_FP
      machineBetheFeasibilityResultCode_mem_FP

/-! ## Exact canonical semantics -/

@[simp] theorem machineOptimizerFeasibilityReducedDimensionUnary_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityReducedDimensionUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate (n - 1) true := by
  rw [machineOptimizerFeasibilityReducedDimensionUnary,
    machineOptimizerFeasibilitySource_encode,
    machineOptimizerFeasibilityReducedDimensionBits_encode]
  apply machineBoundedUnary_encode_of_le
  exact (show n - 1 ≤ (n - 1) ^ 2 + 1 by nlinarith).trans
    (optimizerEllipsoidDimension_le_sourceLength hn A)

@[simp] theorem machineOptimizerFeasibilityTauCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityTauCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode (rawRatOfRat (explicitRegularizationScale n)) := by
  rw [machineOptimizerFeasibilityTauCode,
    machineOptimizerFeasibilitySource_encode,
    machineOptimizerTauRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value, rawOptimizerTau_value,
    rawRatBinaryCode_rawRatOfRat]

@[simp] theorem machineOptimizerFeasibilityDeltaRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityDeltaRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode
        (rawExplicitOptimizerFloor n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerFeasibilityDeltaRawCode,
    machineOptimizerFeasibilitySource_encode,
    machineExplicitOptimizerFloorRawCode_encode hn]
  rfl

@[simp] theorem machineOptimizerFeasibilityOracleStaticCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityOracleStaticCode
        (optimizerFeasibilityCallCode A upper) =
      machineBetheFeasibilityCanonicalStaticWord
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (rawExplicitOptimizerFloor (m + 1)
          (rationalMatrixEntryBitBound A)) upper := by
  rw [machineOptimizerFeasibilityOracleStaticCode,
    machineOptimizerFeasibilityReducedDimensionUnary_encode (by omega),
    machineOptimizerFeasibilitySource_encode,
    machineExplicitOptimizerPrecisionRuler_encode,
    machineOptimizerFeasibilityTauCode_encode,
    machineOptimizerFeasibilityDeltaRawCode_encode (by omega),
    machineOptimizerFeasibilityUpperRawCode_encode,
    machineBetheFeasibilityCanonicalStaticWord]
  have hm1 : m + 1 - 1 = m := by omega
  rw [hm1]

@[simp] theorem machineOptimizerFeasibilityInitialBallCode_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInitialBallCode
        (optimizerFeasibilityCallCode A upper) =
      rationalEllipsoidStateBinaryCode
        (rationalBallEllipsoid ((n - 1) ^ 2 + 1) 0
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value) := by
  rw [machineOptimizerFeasibilityInitialBallCode,
    machineOptimizerFeasibilityEllipsoidDimensionUnary_encode hn,
    machineOptimizerFeasibilityOuterRadiusEntryCode_encode (by omega)]
  change machineRationalBallStateCode
      (machineDiagonalBasisCanonicalInput ((n - 1) ^ 2 + 1)
        (rawOptimizerFeasibilityOuterRadius n
          (rationalMatrixEntryBitBound A) upper).value) = _
  exact machineRationalBallStateCode_encode _ _

@[simp] theorem machineOptimizerFeasibilityLoopWord_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityLoopWord
        (optimizerFeasibilityCallCode A upper) =
      machineBetheFeasibilityCanonicalWord
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (rawExplicitOptimizerFloor (m + 1)
          (rationalMatrixEntryBitBound A)) upper
        (explicitBallFeasibilityPrecision (m * m + 1)
          (betheThresholdFeasibilityBudget m upper.value
            (explicitOptimizerInnerRadius A))
          (betheEpigraphOuterRadius m upper.value
            (explicitOptimizerInnerRadius A)))
        (betheThresholdFeasibilityBudget m upper.value
          (explicitOptimizerInnerRadius A))
        (explicitBallFeasibilityStateCodeBound (m * m + 1)
          (betheThresholdFeasibilityBudget m upper.value
            (explicitOptimizerInnerRadius A))
          (betheEpigraphOuterRadius m upper.value
            (explicitOptimizerInnerRadius A)))
        (rationalBallEllipsoid (m * m + 1) 0
          (betheEpigraphOuterRadius m upper.value
            (explicitOptimizerInnerRadius A))) := by
  have hR := rawOptimizerFeasibilityOuterRadius_eq A upper
  have hr := (rawExplicitOptimizerScales_value A).2.2.2.2
  rw [machineOptimizerFeasibilityLoopWord,
    machineOptimizerFeasibilityBudgetUnary_eq_thresholdBudget hm,
    machineOptimizerFeasibilityStateBoundUnary_encode (by omega),
    machineOptimizerFeasibilityRoundingPrecisionUnary_encode (by omega),
    machineOptimizerFeasibilityOracleStaticCode_encode hm,
    machineOptimizerFeasibilityInitialBallCode_encode (by omega),
    hR, hr]
  have hd : (m + 1 - 1) ^ 2 + 1 = m * m + 1 := by
    have hm1 : m + 1 - 1 = m := by omega
    rw [hm1, pow_two]
  rw [hd]
  rfl

theorem machineExplicitBetheThresholdFeasibilityCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ i j, 0 < A i j) (upper : RawRat) :
    machineExplicitBetheThresholdFeasibilityCode
        (optimizerFeasibilityCallCode A upper) =
      rationalFeasibilityResultBinaryCode
        (runExplicitScannedBetheThresholdFeasibility
          (explicitRegularizationScale (m + 1)) A
          (explicitOptimizerPrecision A)
          (rawExplicitOptimizerFloor (m + 1)
            (rationalMatrixEntryBitBound A)) upper
          (explicitOptimizerInnerRadius A)) := by
  let tau := explicitRegularizationScale (m + 1)
  let delta := rawExplicitOptimizerFloor (m + 1)
    (rationalMatrixEntryBitBound A)
  let r := explicitOptimizerInnerRadius A
  let R := betheEpigraphOuterRadius m upper.value r
  let T := betheThresholdFeasibilityBudget m upper.value r
  have htau0 : 0 ≤ tau := (explicitRegularizationScale_pos (by omega)).le
  have htau1 : tau ≤ 1 := explicitRegularizationScale_le_one (by omega)
  have hdelta : 0 < delta.value := by
    simpa only [delta, (rawExplicitOptimizerScales_value A).1] using!
      explicitOptimizerFloor_pos A
  have hr : 0 < r := explicitOptimizerInnerRadius_pos A
  have hR : 0 < R := betheEpigraphOuterRadius_pos m hr.le
  rw [machineExplicitBetheThresholdFeasibilityCode,
    machineOptimizerFeasibilityLoopWord_encode hm]
  have hmachine := machineExplicitBallBetheFeasibilityResultCode_encode
    hm htau0 htau1 hA (explicitOptimizerPrecision A) hdelta upper T hR
  simpa only [tau, delta, r, R, T,
    runExplicitScannedBetheThresholdFeasibility] using! hmachine

end BeyondBethe
