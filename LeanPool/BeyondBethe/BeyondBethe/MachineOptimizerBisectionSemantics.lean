/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerBisectionLoop
public import Mathlib.Tactic

/-!
# Exact semantics of the dyadic optimizer bisection machine

This file proves that the finite-word loop queries exactly the rational
midpoints of the row-major semantic bisection.  No numerical interpretation
is inferred from a decoder: every intermediate word is reduced to the
canonical project encoding of its stated rational value.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

@[simp] theorem rawOptimizerInitialLow_value (n : ℕ) :
    (rawOptimizerInitialLow n).value = -(2 * n ^ 2 : ℚ) := by
  simp [rawOptimizerInitialLow, rawOptimizerTwiceNSquare,
    rawOptimizerTwo, rawOptimizerNSquare, rawOptimizerDimension]
  ring

theorem explicitOptimizerInitialWidth_eq_interval {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerInitialWidth A =
      betheBisectionInitialHigh A (explicitOptimizerMix A)
          (explicitOptimizerInnerRadius A) -
        betheNegativeObjectiveLower m := by
  rfl

@[simp] theorem optimizerDyadicThreshold_zero {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    optimizerDyadicThreshold A 0 0 = betheNegativeObjectiveLower m := by
  simp [optimizerDyadicThreshold]

@[simp] theorem optimizerDyadicThreshold_one_zero {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    optimizerDyadicThreshold A 1 0 =
      betheBisectionInitialHigh A (explicitOptimizerMix A)
        (explicitOptimizerInnerRadius A) := by
  rw [optimizerDyadicThreshold, pow_zero, div_one,
    explicitOptimizerInitialWidth_eq_interval]
  norm_num

/-- The raw-rational dyadic fraction `k/2^t`. -/
def rawDyadicFraction (k t : ℕ) : RawRat :=
  ⟨k, 2 ^ t, pow_pos (by omega) _⟩

@[simp] theorem rawDyadicFraction_value (k t : ℕ) :
    (rawDyadicFraction k t).value = (k : ℚ) / 2 ^ t := by
  simp [rawDyadicFraction, RawRat.value]

/-- Encodes a matrix, scheduled iteration ruler, binary index `k`, and unary depth `t` as
bisection state. -/
def machineOptimizerBisectionCanonicalState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (k t : ℕ) : List Bool :=
  machineOptimizerBisectionStatePack
    (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩)
    (List.replicate (explicitOptimizerBisectionSteps A) true)
    k.bits (List.replicate t true)

@[simp] theorem machineOptimizerBisectionCanonicalState_source {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionStateSource
        (machineOptimizerBisectionCanonicalState A k t) =
      rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩ := by
  simp [machineOptimizerBisectionCanonicalState]

@[simp] theorem machineOptimizerBisectionCanonicalState_ruler {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionStateRuler
        (machineOptimizerBisectionCanonicalState A k t) =
      List.replicate (explicitOptimizerBisectionSteps A) true := by
  simp [machineOptimizerBisectionCanonicalState]

@[simp] theorem machineOptimizerBisectionCanonicalState_index {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionStateIndex
        (machineOptimizerBisectionCanonicalState A k t) = k.bits := by
  simp [machineOptimizerBisectionCanonicalState]

@[simp] theorem machineOptimizerBisectionCanonicalState_depth {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionStateDepth
        (machineOptimizerBisectionCanonicalState A k t) =
      List.replicate t true := by
  simp [machineOptimizerBisectionCanonicalState]

@[simp] theorem machineOptimizerInitialLowEntryCode_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineOptimizerInitialLowEntryCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rawRatBinaryCode
        (rawRatOfRat (betheNegativeObjectiveLower m)) := by
  rw [machineOptimizerInitialLowEntryCode,
    machineOptimizerTwiceNSquareForWidthRawCode_encode,
    machineRawRatNegCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value,
    RawRat.value_neg, rawOptimizerTwiceNSquare, RawRat.value_mul]
  simp [rawOptimizerTwo, rawOptimizerNSquare,
    rawOptimizerDimension, betheNegativeObjectiveLower]
  ring

@[simp] theorem machineOptimizerInitialWidthEntryCodeForBisection_encode
    {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineOptimizerInitialWidthEntryCodeForBisection
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rawRatBinaryCode (rawRatOfRat (explicitOptimizerInitialWidth A)) := by
  rw [machineOptimizerInitialWidthEntryCodeForBisection,
    machineExplicitOptimizerInitialWidthRawCode_encode (by omega),
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value,
    rawExplicitOptimizerInitialWidth_eq]

@[simp] theorem machineOptimizerBisectionEvenIndexBits_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionEvenIndexBits
        (machineOptimizerBisectionCanonicalState A k t) =
      (2 * k).bits := by
  rw [machineOptimizerBisectionEvenIndexBits,
    machineOptimizerBisectionCanonicalState_index]
  change machineBinaryMulBits (pair k.bits (2 : ℕ).bits) = _
  rw [machineBinaryMulBits_pair_natBits]
  congr 1
  omega

@[simp] theorem machineOptimizerBisectionOddIndexBits_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionOddIndexBits
        (machineOptimizerBisectionCanonicalState A k t) =
      (2 * k + 1).bits := by
  rw [machineOptimizerBisectionOddIndexBits,
    machineOptimizerBisectionEvenIndexBits_encode]
  change machineBinaryAddBits (pair (2 * k).bits (1 : ℕ).bits) = _
  rw [machineBinaryAddBits_pair_natBits]

@[simp] theorem machineOptimizerBisectionNextDepth_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionNextDepth
        (machineOptimizerBisectionCanonicalState A k t) =
      List.replicate (t + 1) true := by
  rw [machineOptimizerBisectionNextDepth,
    machineOptimizerBisectionCanonicalState_depth,
    List.replicate_succ]

@[simp] theorem machineOptimizerBisectionDenominatorBits_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionDenominatorBits
        (machineOptimizerBisectionCanonicalState A k t) =
      (2 ^ (t + 1)).bits := by
  rw [machineOptimizerBisectionDenominatorBits,
    machineOptimizerBisectionNextDepth_encode,
    machineDirectedLogPowerTwoBits_encode, List.length_replicate]

@[simp] theorem machineOptimizerBisectionFractionRawCode_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionFractionRawCode
        (machineOptimizerBisectionCanonicalState A k t) =
      rawRatBinaryCode (rawDyadicFraction (2 * k + 1) (t + 1)) := by
  rw [machineOptimizerBisectionFractionRawCode,
    machineOptimizerBisectionOddIndexBits_encode,
    machineOptimizerBisectionDenominatorBits_encode,
    machineNaturalIntegerCode_natBits]
  rfl

@[simp] theorem machineOptimizerBisectionMidpointRawCode_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionMidpointRawCode
        (machineOptimizerBisectionCanonicalState A k t) =
      rawRatBinaryCode
        (rawRatOfRat (optimizerDyadicThreshold A (2 * k + 1) (t + 1))) := by
  rw [machineOptimizerBisectionMidpointRawCode,
    machineOptimizerBisectionMidpointUnnormalizedRawCode,
    machineOptimizerBisectionScaledFractionRawCode,
    machineOptimizerBisectionCanonicalState_source,
    machineOptimizerBisectionFractionRawCode_encode,
    machineOptimizerInitialWidthEntryCodeForBisection_encode,
    machineRawRatMulCode_encode,
    machineOptimizerInitialLowEntryCode_encode,
    machineRawRatAddCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value,
    RawRat.value_add, RawRat.value_mul, rawRatOfRat_value,
    rawRatOfRat_value, rawDyadicFraction_value]
  rfl

@[simp] theorem machineOptimizerBisectionFeasibilityResult_encode {m : ℕ}
    (hm : 0 < m) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ i j, 0 < A i j) (k t : ℕ) :
    machineOptimizerBisectionFeasibilityResult
        (machineOptimizerBisectionCanonicalState A k t) =
      rationalFeasibilityResultBinaryCode
        (runExplicitScannedBetheThresholdFeasibility
          (explicitRegularizationScale (m + 1)) A
          (explicitOptimizerPrecision A)
          (rawExplicitOptimizerFloor (m + 1)
            (rationalMatrixEntryBitBound A))
          (rawRatOfRat
            (optimizerDyadicThreshold A (2 * k + 1) (t + 1)))
          (explicitOptimizerInnerRadius A)) := by
  rw [machineOptimizerBisectionFeasibilityResult,
    machineOptimizerBisectionFeasibilityCall,
    machineOptimizerBisectionCanonicalState_source,
    machineOptimizerBisectionMidpointRawCode_encode]
  exact machineExplicitBetheThresholdFeasibilityCode_encode hm A hA _

/-! ## Indexed semantic loop and exact step simulation -/

/-- Updates the dyadic index to `2*k` on midpoint acceptance or `2*k + 1` on exhaustion. -/
def scannedOptimizerIndexStep {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (k t : ℕ) : ℕ :=
  match runExplicitScannedBetheThresholdFeasibility
      (explicitRegularizationScale (m + 1)) A
      (explicitOptimizerPrecision A)
      (rawExplicitOptimizerFloor (m + 1)
        (rationalMatrixEntryBitBound A))
      (rawRatOfRat
        (optimizerDyadicThreshold A (2 * k + 1) (t + 1)))
      (explicitOptimizerInnerRadius A) with
  | .accepted _ => 2 * k
  | .exhausted _ => 2 * k + 1

/-- Runs the semantic dyadic-index update for a specified number of steps from depth `t` and
index `k`. -/
def runScannedOptimizerIndex {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    ℕ → ℕ → ℕ → ℕ
  | 0, _t, k => k
  | N + 1, t, k =>
      runScannedOptimizerIndex A N (t + 1)
        (scannedOptimizerIndexStep A k t)

theorem machineOptimizerBisectionStep_encode {m : ℕ}
    (hm : 0 < m) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ i j, 0 < A i j) (k t : ℕ) :
    machineOptimizerBisectionStep
        (machineOptimizerBisectionCanonicalState A k t) =
      machineOptimizerBisectionCanonicalState A
        (scannedOptimizerIndexStep A k t) (t + 1) := by
  rw [machineOptimizerBisectionStep,
    machineOptimizerBisectionCanonicalState_source,
    machineOptimizerBisectionCanonicalState_ruler,
    machineOptimizerBisectionNextDepth_encode,
    machineOptimizerBisectionNextIndexBits,
    machineOptimizerBisectionExhaustedBit,
    machineOptimizerBisectionFeasibilityResult_encode hm A hA]
  cases hrun : runExplicitScannedBetheThresholdFeasibility
      (explicitRegularizationScale (m + 1)) A
      (explicitOptimizerPrecision A)
      (rawExplicitOptimizerFloor (m + 1)
        (rationalMatrixEntryBitBound A))
      (rawRatOfRat
        (optimizerDyadicThreshold A (2 * k + 1) (t + 1)))
      (explicitOptimizerInnerRadius A) with
  | accepted q =>
      simp only [rationalFeasibilityResultBinaryCode,
        scannedOptimizerIndexStep, hrun,
        machinePairFirst_pair, machineHeadBit_cons,
        machineIfHead_false]
      rw [machineOptimizerBisectionEvenIndexBits_encode]
      rfl
  | exhausted E =>
      simp only [rationalFeasibilityResultBinaryCode,
        scannedOptimizerIndexStep, hrun,
        machinePairFirst_pair, machineHeadBit_cons,
        machineIfHead_true]
      rw [machineOptimizerBisectionOddIndexBits_encode]
      rfl

theorem machineOptimizerBisectionIterate_encode {m : ℕ}
    (hm : 0 < m) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ i j, 0 < A i j) (k t : ℕ) : ∀ N : ℕ,
    (machineOptimizerBisectionStep)^[N]
        (machineOptimizerBisectionCanonicalState A k t) =
      machineOptimizerBisectionCanonicalState A
        (runScannedOptimizerIndex A N t k) (t + N) := by
  intro N
  induction N generalizing k t with
  | zero => simp [runScannedOptimizerIndex]
  | succ N ih =>
      rw [Function.iterate_succ_apply,
        machineOptimizerBisectionStep_encode hm A hA,
        ih, runScannedOptimizerIndex]
      have ht : t + 1 + N = t + (N + 1) := by omega
      rw [ht]

@[simp] theorem machineOptimizerBisectionInit_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineOptimizerBisectionInit
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      machineOptimizerBisectionCanonicalState A 0 0 := by
  rw [machineOptimizerBisectionInit,
    machineExplicitOptimizerBisectionStepsRuler_encode]
  rfl

@[simp] theorem machineOptimizerBisectionFinalState_encode {m : ℕ}
    (hm : 0 < m) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ i j, 0 < A i j) :
    machineOptimizerBisectionFinalState
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      machineOptimizerBisectionCanonicalState A
        (runScannedOptimizerIndex A (explicitOptimizerBisectionSteps A) 0 0)
        (explicitOptimizerBisectionSteps A) := by
  rw [machineOptimizerBisectionFinalState,
    machineExplicitOptimizerBisectionStepsRuler_encode,
    List.length_replicate, machineOptimizerBisectionInit_encode,
    machineOptimizerBisectionIterate_encode hm A hA]
  simp

@[simp] theorem machineOptimizerBisectionHighIndexBits_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionHighIndexBits
        (machineOptimizerBisectionCanonicalState A k t) =
      (k + 1).bits := by
  rw [machineOptimizerBisectionHighIndexBits,
    machineOptimizerBisectionCanonicalState_index]
  change machineBinaryAddBits (pair k.bits (1 : ℕ).bits) = _
  rw [machineBinaryAddBits_pair_natBits]

@[simp] theorem machineOptimizerBisectionHighFractionRawCode_encode
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (k t : ℕ) :
    machineOptimizerBisectionHighFractionRawCode
        (machineOptimizerBisectionCanonicalState A k t) =
      rawRatBinaryCode (rawDyadicFraction (k + 1) t) := by
  rw [machineOptimizerBisectionHighFractionRawCode,
    machineOptimizerBisectionHighIndexBits_encode,
    machineOptimizerBisectionCanonicalState_depth,
    machineNaturalIntegerCode_natBits,
    machineDirectedLogPowerTwoBits_encode, List.length_replicate]
  rfl

@[simp] theorem machineOptimizerBisectionHighRawCode_encode {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    machineOptimizerBisectionHighRawCode
        (machineOptimizerBisectionCanonicalState A k t) =
      rawRatBinaryCode
        (rawRatOfRat (optimizerDyadicThreshold A (k + 1) t)) := by
  rw [machineOptimizerBisectionHighRawCode,
    machineOptimizerBisectionHighUnnormalizedRawCode,
    machineOptimizerBisectionHighScaledRawCode,
    machineOptimizerBisectionCanonicalState_source,
    machineOptimizerBisectionHighFractionRawCode_encode,
    machineOptimizerInitialWidthEntryCodeForBisection_encode,
    machineRawRatMulCode_encode,
    machineOptimizerInitialLowEntryCode_encode,
    machineRawRatAddCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value,
    RawRat.value_add, RawRat.value_mul, rawRatOfRat_value,
    rawRatOfRat_value, rawDyadicFraction_value]
  rfl

/-! ## Equivalence with ordinary midpoint bisection -/

theorem optimizerDyadicThreshold_even {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    optimizerDyadicThreshold A (2 * k) (t + 1) =
      optimizerDyadicThreshold A k t := by
  simp only [optimizerDyadicThreshold]
  push_cast
  rw [pow_succ]
  ring

theorem optimizerDyadicThreshold_odd_midpoint {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    optimizerDyadicThreshold A (2 * k + 1) (t + 1) =
      (optimizerDyadicThreshold A k t +
        optimizerDyadicThreshold A (k + 1) t) / 2 := by
  simp only [optimizerDyadicThreshold]
  push_cast
  rw [pow_succ]
  ring

theorem optimizerDyadicThreshold_odd_high {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (k t : ℕ) :
    optimizerDyadicThreshold A (2 * k + 1 + 1) (t + 1) =
      optimizerDyadicThreshold A (k + 1) t := by
  simp only [optimizerDyadicThreshold]
  push_cast
  rw [pow_succ]
  ring

/-- Relates a bisection state's endpoints to adjacent dyadic thresholds with index `k` and depth
`t`. -/
def ScannedOptimizerIndexAgrees {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (s : BetheBisectionState (m * m + 1)) (k t : ℕ) : Prop :=
  s.low = optimizerDyadicThreshold A k t ∧
    s.high = optimizerDyadicThreshold A (k + 1) t

theorem initialScannedOptimizerIndexAgrees {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    ScannedOptimizerIndexAgrees A
      (initialScannedBetheBisectionState
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (rawExplicitOptimizerFloor (m + 1)
          (rationalMatrixEntryBitBound A))
        (explicitOptimizerMix A) (explicitOptimizerInnerRadius A)) 0 0 := by
  constructor
  · rw [initialScannedBetheBisectionState_low,
      optimizerDyadicThreshold_zero]
  · rw [initialScannedBetheBisectionState_high,
      optimizerDyadicThreshold_one_zero]

theorem scannedOptimizerIndexStep_agrees {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    {s : BetheBisectionState (m * m + 1)} {k t : ℕ}
    (hs : ScannedOptimizerIndexAgrees A s k t) :
    ScannedOptimizerIndexAgrees A
      (scannedBetheBisectionStep
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (rawExplicitOptimizerFloor (m + 1)
          (rationalMatrixEntryBitBound A))
        (explicitOptimizerInnerRadius A) s)
      (scannedOptimizerIndexStep A k t) (t + 1) := by
  rcases hs with ⟨hlow, hhigh⟩
  rw [scannedBetheBisectionStep]
  have hmid : (s.low + s.high) / 2 =
      optimizerDyadicThreshold A (2 * k + 1) (t + 1) := by
    rw [hlow, hhigh, optimizerDyadicThreshold_odd_midpoint]
  rw [hmid]
  cases hrun : runExplicitScannedBetheThresholdFeasibility
      (explicitRegularizationScale (m + 1)) A
      (explicitOptimizerPrecision A)
      (rawExplicitOptimizerFloor (m + 1)
        (rationalMatrixEntryBitBound A))
      (rawRatOfRat
        (optimizerDyadicThreshold A (2 * k + 1) (t + 1)))
      (explicitOptimizerInnerRadius A) with
  | accepted q =>
      simp only [scannedOptimizerIndexStep, hrun]
      constructor
      · simpa only [optimizerDyadicThreshold_even] using! hlow
      · rfl
  | exhausted E =>
      simp only [scannedOptimizerIndexStep, hrun]
      constructor
      · rfl
      · simpa only [optimizerDyadicThreshold_odd_high] using! hhigh

theorem runScannedOptimizerIndex_agrees {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    {s : BetheBisectionState (m * m + 1)} {k t : ℕ}
    (hs : ScannedOptimizerIndexAgrees A s k t) : ∀ N : ℕ,
    ScannedOptimizerIndexAgrees A
      (runScannedBetheBisection
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (rawExplicitOptimizerFloor (m + 1)
          (rationalMatrixEntryBitBound A))
        (explicitOptimizerInnerRadius A) N s)
      (runScannedOptimizerIndex A N t k) (t + N) := by
  intro N
  induction N generalizing s k t with
  | zero => simpa [runScannedBetheBisection,
      runScannedOptimizerIndex] using! hs
  | succ N ih =>
      rw [runScannedBetheBisection, runScannedOptimizerIndex]
      have hstep := scannedOptimizerIndexStep_agrees A hs
      simpa only [Nat.add_assoc, Nat.add_comm 1 N] using! ih hstep

end BeyondBethe
