/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFeasibilityFit
import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerRoundingSchedule

/-!
# Finite-word state ruler for one optimizer feasibility call

The feasibility loop truncates every updated ellipsoid to a stored unary
ruler in order to remain polynomial-time on malformed words.  This file
computes the proved ordinary-binary state bound from the same finite-word
dimension, budget, magnitude, and precision schedules used by the call.
-/

namespace BeyondBethe

open Complexity

def machineOptimizerFeasibilityStateDenominatorBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityRoundingPrecisionBits
    (machineBinaryAddOf (machineBinaryConst 10)
      (machineBinaryMulOf (machineBinaryConst 4)
        machineOptimizerFeasibilityDBits)) word

def machineOptimizerFeasibilityStateTwiceMagnitudeBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 2)
    machineOptimizerFeasibilityKPlusGrowthBits word

def machineOptimizerFeasibilityStateFourDenominatorBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 4)
    machineOptimizerFeasibilityStateDenominatorBits word

def machineOptimizerFeasibilityStateEntryFirstBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf (machineBinaryConst 8)
    machineOptimizerFeasibilityStateTwiceMagnitudeBits word

def machineOptimizerFeasibilityStateEntryBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityStateEntryFirstBits
    machineOptimizerFeasibilityStateFourDenominatorBits word

def machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf
    (machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateEntryBits)
    (machineBinaryConst 2) word

def machineOptimizerFeasibilityStateVectorBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf machineOptimizerFeasibilityDBits
    machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits word

def machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf
    (machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateVectorBits)
    (machineBinaryConst 2) word

def machineOptimizerFeasibilityStateMatrixBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf machineOptimizerFeasibilityDBits
    machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits word

def machineOptimizerFeasibilityStateDimensionTermBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 2)
    (machineBinaryAddOf machineOptimizerFeasibilityDBits
      (machineBinaryConst 1)) word

def machineOptimizerFeasibilityStateInnerFirstBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf
    (machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateVectorBits)
    (machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateMatrixBits) word

def machineOptimizerFeasibilityStateInnerBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityStateInnerFirstBits
    (machineBinaryConst 2) word

def machineOptimizerFeasibilityStateTwiceInnerBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 2)
    machineOptimizerFeasibilityStateInnerBits word

def machineOptimizerFeasibilityStateBoundFirstBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityStateDimensionTermBits
    machineOptimizerFeasibilityStateTwiceInnerBits word

def machineOptimizerFeasibilityStateBoundBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityStateBoundFirstBits
    (machineBinaryConst 2) word

def machineOptimizerFeasibilityStateGuardSource
    (word : List Bool) : List Bool :=
  machineOptimizerFeasibilityEllipsoidDimensionUnary word ++
    (machineOptimizerFeasibilityInitialMagnitudeLengthRuler word ++
      (machineOptimizerFeasibilityBudgetUnary word ++
        machineOptimizerFeasibilityRoundingPrecisionUnary word))

def machineOptimizerFeasibilityStateGuard
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 3
    (machineOptimizerFeasibilityStateGuardSource word)

def machineOptimizerFeasibilityStateBoundUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerFeasibilityStateGuard word)
      (machineOptimizerFeasibilityStateBoundBits word))

/-! ## Polynomial-time closure -/

theorem machineOptimizerFeasibilityStateDenominatorBits_mem_FP :
    machineOptimizerFeasibilityStateDenominatorBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityRoundingPrecisionBits_mem_FP
    (machineBinaryAddOf_mem_FP (machineBinaryConst_mem_FP 10)
      (machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 4)
        machineOptimizerFeasibilityDBits_mem_FP))

theorem machineOptimizerFeasibilityStateTwiceMagnitudeBits_mem_FP :
    machineOptimizerFeasibilityStateTwiceMagnitudeBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
    machineOptimizerFeasibilityKPlusGrowthBits_mem_FP

theorem machineOptimizerFeasibilityStateFourDenominatorBits_mem_FP :
    machineOptimizerFeasibilityStateFourDenominatorBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 4)
    machineOptimizerFeasibilityStateDenominatorBits_mem_FP

theorem machineOptimizerFeasibilityStateEntryFirstBits_mem_FP :
    machineOptimizerFeasibilityStateEntryFirstBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP (machineBinaryConst_mem_FP 8)
    machineOptimizerFeasibilityStateTwiceMagnitudeBits_mem_FP

theorem machineOptimizerFeasibilityStateEntryBits_mem_FP :
    machineOptimizerFeasibilityStateEntryBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityStateEntryFirstBits_mem_FP
    machineOptimizerFeasibilityStateFourDenominatorBits_mem_FP

theorem machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits_mem_FP :
    machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    (machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
      machineOptimizerFeasibilityStateEntryBits_mem_FP)
    (machineBinaryConst_mem_FP 2)

theorem machineOptimizerFeasibilityStateVectorBits_mem_FP :
    machineOptimizerFeasibilityStateVectorBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP machineOptimizerFeasibilityDBits_mem_FP
    machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits_mem_FP

theorem machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits_mem_FP :
    machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    (machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
      machineOptimizerFeasibilityStateVectorBits_mem_FP)
    (machineBinaryConst_mem_FP 2)

theorem machineOptimizerFeasibilityStateMatrixBits_mem_FP :
    machineOptimizerFeasibilityStateMatrixBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP machineOptimizerFeasibilityDBits_mem_FP
    machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits_mem_FP

theorem machineOptimizerFeasibilityStateDimensionTermBits_mem_FP :
    machineOptimizerFeasibilityStateDimensionTermBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
    (machineBinaryAddOf_mem_FP machineOptimizerFeasibilityDBits_mem_FP
      (machineBinaryConst_mem_FP 1))

theorem machineOptimizerFeasibilityStateInnerFirstBits_mem_FP :
    machineOptimizerFeasibilityStateInnerFirstBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    (machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
      machineOptimizerFeasibilityStateVectorBits_mem_FP)
    (machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
      machineOptimizerFeasibilityStateMatrixBits_mem_FP)

theorem machineOptimizerFeasibilityStateInnerBits_mem_FP :
    machineOptimizerFeasibilityStateInnerBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityStateInnerFirstBits_mem_FP
    (machineBinaryConst_mem_FP 2)

theorem machineOptimizerFeasibilityStateTwiceInnerBits_mem_FP :
    machineOptimizerFeasibilityStateTwiceInnerBits ∈ FP := by
  exact machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
    machineOptimizerFeasibilityStateInnerBits_mem_FP

theorem machineOptimizerFeasibilityStateBoundFirstBits_mem_FP :
    machineOptimizerFeasibilityStateBoundFirstBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityStateDimensionTermBits_mem_FP
    machineOptimizerFeasibilityStateTwiceInnerBits_mem_FP

theorem machineOptimizerFeasibilityStateBoundBits_mem_FP :
    machineOptimizerFeasibilityStateBoundBits ∈ FP := by
  exact machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityStateBoundFirstBits_mem_FP
    (machineBinaryConst_mem_FP 2)

theorem machineOptimizerFeasibilityStateGuardSource_mem_FP :
    machineOptimizerFeasibilityStateGuardSource ∈ FP := by
  exact machineAppend_mem_FP
    machineOptimizerFeasibilityEllipsoidDimensionUnary_mem_FP
    (machineAppend_mem_FP
      machineOptimizerFeasibilityInitialMagnitudeLengthRuler_mem_FP
      (machineAppend_mem_FP machineOptimizerFeasibilityBudgetUnary_mem_FP
        machineOptimizerFeasibilityRoundingPrecisionUnary_mem_FP))

theorem machineOptimizerFeasibilityStateGuard_mem_FP :
    machineOptimizerFeasibilityStateGuard ∈ FP := by
  simpa only [machineOptimizerFeasibilityStateGuard] using!
    machineCompose_mem_FP
      machineOptimizerFeasibilityStateGuardSource_mem_FP
      (machineIteratedBinaryWidth_mem_FP 3)

theorem machineOptimizerFeasibilityStateBoundUnary_mem_FP :
    machineOptimizerFeasibilityStateBoundUnary ∈ FP := by
  simpa only [machineOptimizerFeasibilityStateBoundUnary] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityStateGuard_mem_FP
        machineOptimizerFeasibilityStateBoundBits_mem_FP)
      machineBoundedUnary_mem_FP

/-! ## Exact semantics -/

theorem machineOptimizerFeasibilityStateBoundBits_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityStateBoundBits
        (optimizerFeasibilityCallCode A upper) =
      (explicitBallFeasibilityStateCodeBound
        ((n - 1) ^ 2 + 1)
        (betheThresholdFeasibilityBudget (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value)
        (rawOptimizerFeasibilityOuterRadius n
          (rationalMatrixEntryBitBound A) upper).value).bits := by
  let word := optimizerFeasibilityCallCode A upper
  let d := (n - 1) ^ 2 + 1
  let T := betheThresholdFeasibilityBudget (n - 1) upper.value
    (rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value
  let R := (rawOptimizerFeasibilityOuterRadius n
    (rationalMatrixEntryBitBound A) upper).value
  let K := explicitBallInitialMagnitudeExponent d R
  let p := explicitBallFeasibilityPrecision d T R
  let KS := K + T * (6 + 3 * d)
  let P := p + 10 + 4 * d
  let e := rationalEntryMachineCodeBound KS P
  let v := rationalVectorMachineCodeBound d KS P
  let M := rationalMatrixMachineCodeBound d KS P
  have hRthreshold :
      (rawOptimizerFeasibilityOuterRadius n
        (rationalMatrixEntryBitBound A) upper).value =
        betheEpigraphOuterRadius (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value := by
    rw [rawOptimizerFeasibilityOuterRadius_value,
      betheEpigraphOuterRadius]
    push_cast
    rw [pow_two]
  have hd : machineOptimizerFeasibilityDBits word = d.bits := by
    simpa only [machineOptimizerFeasibilityDBits, word, d] using!
      machineOptimizerFeasibilityEllipsoidDimensionBits_encode A upper
  have hT : machineOptimizerFeasibilityBudgetBits word = T.bits := by
    have h := machineOptimizerFeasibilityBudgetBits_encode hn A upper
    rw [hRthreshold] at h
    simpa only [word, T, betheThresholdFeasibilityBudget, pow_two] using! h
  have hK : machineOptimizerFeasibilityKBits word = K.bits := by
    have hruler :
        machineOptimizerFeasibilityInitialMagnitudeLengthRuler word =
          List.replicate K true := by
      simpa only [word, K, d, R] using!
        machineOptimizerFeasibilityInitialMagnitudeLengthRuler_encode hn A upper
    rw [machineOptimizerFeasibilityKBits, hruler,
      machineLengthBits_encode, List.length_replicate]
  have hp : machineOptimizerFeasibilityRoundingPrecisionBits word = p.bits := by
    simpa only [word, p, d, T, R] using!
      machineOptimizerFeasibilityRoundingPrecisionBits_encode hn A upper
  have h3d : machineOptimizerFeasibilityThreeDBits word = (3 * d).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hd
  have hgrowth : machineOptimizerFeasibilitySixPlusThreeDBits word =
      (6 + 3 * d).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ rfl h3d
  have hTgrowth : machineOptimizerFeasibilityTTimesGrowthBits word =
      (T * (6 + 3 * d)).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ hT hgrowth
  have hKS : machineOptimizerFeasibilityKPlusGrowthBits word = KS.bits := by
    simpa only [KS] using!
      machineBinaryAddOf_natBits _ _ _ _ _ hK hTgrowth
  have h4d : machineBinaryMulOf (machineBinaryConst 4)
      machineOptimizerFeasibilityDBits word = (4 * d).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hd
  have h10plus4d : machineBinaryAddOf (machineBinaryConst 10)
      (machineBinaryMulOf (machineBinaryConst 4)
        machineOptimizerFeasibilityDBits) word = (10 + 4 * d).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ rfl h4d
  have hP : machineOptimizerFeasibilityStateDenominatorBits word = P.bits := by
    simpa only [machineOptimizerFeasibilityStateDenominatorBits, P,
      Nat.add_assoc] using!
      machineBinaryAddOf_natBits _ _ _ _ _ hp h10plus4d
  have h2KS : machineOptimizerFeasibilityStateTwiceMagnitudeBits word =
      (2 * KS).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hKS
  have h4P : machineOptimizerFeasibilityStateFourDenominatorBits word =
      (4 * P).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hP
  have h8plus2KS : machineOptimizerFeasibilityStateEntryFirstBits word =
      (8 + 2 * KS).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ rfl h2KS
  have he : machineOptimizerFeasibilityStateEntryBits word = e.bits := by
    simpa only [e, rationalEntryMachineCodeBound] using!
      machineBinaryAddOf_natBits _ _ _ _ _ h8plus2KS h4P
  have h2e : machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateEntryBits word = (2 * e).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl he
  have h2e2 : machineOptimizerFeasibilityStateTwiceEntryPlusTwoBits word =
      (2 * e + 2).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ h2e rfl
  have hv : machineOptimizerFeasibilityStateVectorBits word = v.bits := by
    simpa only [v, rationalVectorMachineCodeBound] using!
      machineBinaryMulOf_natBits _ _ _ _ _ hd h2e2
  have h2v : machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateVectorBits word = (2 * v).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hv
  have h2v2 : machineOptimizerFeasibilityStateTwiceVectorPlusTwoBits word =
      (2 * v + 2).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ h2v rfl
  have hM : machineOptimizerFeasibilityStateMatrixBits word = M.bits := by
    simpa only [M, rationalMatrixMachineCodeBound] using!
      machineBinaryMulOf_natBits _ _ _ _ _ hd h2v2
  have hd1 : machineBinaryAddOf machineOptimizerFeasibilityDBits
      (machineBinaryConst 1) word = (d + 1).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hd rfl
  have hdim : machineOptimizerFeasibilityStateDimensionTermBits word =
      (2 * (d + 1)).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hd1
  have h2v' : machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateVectorBits word = (2 * v).bits := h2v
  have h2M : machineBinaryMulOf (machineBinaryConst 2)
      machineOptimizerFeasibilityStateMatrixBits word = (2 * M).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hM
  have hinnerFirst : machineOptimizerFeasibilityStateInnerFirstBits word =
      (2 * v + 2 * M).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ h2v' h2M
  have hinner : machineOptimizerFeasibilityStateInnerBits word =
      (2 * v + 2 * M + 2).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hinnerFirst rfl
  have htwiceInner : machineOptimizerFeasibilityStateTwiceInnerBits word =
      (2 * (2 * v + 2 * M + 2)).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hinner
  have hfirst : machineOptimizerFeasibilityStateBoundFirstBits word =
      (2 * (d + 1) + 2 * (2 * v + 2 * M + 2)).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hdim htwiceInner
  rw [machineOptimizerFeasibilityStateBoundBits]
  rw [machineBinaryAddOf_natBits _ _ word _ _ hfirst rfl]
  simp only [explicitBallFeasibilityStateCodeBound,
    scheduledFeasibilityStateCodeBound, rationalEllipsoidMachineCodeBound,
    rationalVectorMachineCodeBound, rationalMatrixMachineCodeBound,
    rationalEntryMachineCodeBound, explicitBallFeasibilityPrecision,
    d, T, R, K, p, KS, P, e, v, M]

theorem optimizerFeasibilityStateBound_le_guardPolynomial
    (d K T p : ℕ) :
    rationalEllipsoidMachineCodeBound d
        (K + T * (6 + 3 * d)) (p + 10 + 4 * d) ≤
      certificateExpGuardWidth 3 (d + K + T + p) := by
  let Q := d + K + T + p
  have hd : d ≤ Q := by omega
  have hK : K ≤ Q := by omega
  have hT : T ≤ Q := by omega
  have hp : p ≤ Q := by omega
  have hcoarse :
      rationalEllipsoidMachineCodeBound d
          (K + T * (6 + 3 * d)) (p + 10 + 4 * d) ≤
        256 * (Q + 1) ^ 4 + 256 := by
    simp only [rationalEllipsoidMachineCodeBound,
      rationalMatrixMachineCodeBound, rationalVectorMachineCodeBound,
      rationalEntryMachineCodeBound]
    nlinarith [Nat.mul_le_mul hd hd, Nat.mul_le_mul hT hd,
      Nat.mul_le_mul hK hd, Nat.mul_le_mul hp hd,
      Nat.pow_le_pow_left (Nat.le_add_right Q 1) 2,
      Nat.pow_le_pow_left (Nat.le_add_right Q 1) 3,
      Nat.pow_le_pow_left (Nat.le_add_right Q 1) 4]
  have hmain : 256 * (Q + 1) ^ 4 + 256 ≤ (Q + 16) ^ 8 := by
    nlinarith [Nat.pow_le_pow_left (by omega : 4 ≤ Q + 16) 4,
      Nat.pow_le_pow_left (by omega : Q + 1 ≤ Q + 16) 4]
  exact hcoarse.trans <| hmain.trans <| by
    simpa only [Q] using! certificateExpGuardWidth_pow_lower 2 Q

@[simp] theorem machineOptimizerFeasibilityStateGuardSource_length_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    (machineOptimizerFeasibilityStateGuardSource
      (optimizerFeasibilityCallCode A upper)).length =
      ((n - 1) ^ 2 + 1) +
        explicitBallInitialMagnitudeExponent ((n - 1) ^ 2 + 1)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value +
        betheThresholdFeasibilityBudget (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value +
        explicitBallFeasibilityPrecision ((n - 1) ^ 2 + 1)
          (betheThresholdFeasibilityBudget (n - 1) upper.value
            (rawExplicitOptimizerInnerRadius n
              (rationalMatrixEntryBitBound A)).value)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value := by
  have hRthreshold :
      (rawOptimizerFeasibilityOuterRadius n
        (rationalMatrixEntryBitBound A) upper).value =
        betheEpigraphOuterRadius (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value := by
    rw [rawOptimizerFeasibilityOuterRadius_value,
      betheEpigraphOuterRadius]
    push_cast
    rw [pow_two]
  have hbudget :
      32 * (((n - 1) ^ 2 + 1) ^ 3) *
          rationalBallDyadicExponent ((n - 1) ^ 2 + 1)
            (rawOptimizerFeasibilityOuterRadius n
              (rationalMatrixEntryBitBound A) upper).value
            (rawExplicitOptimizerInnerRadius n
              (rationalMatrixEntryBitBound A)).value =
        betheThresholdFeasibilityBudget (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value := by
    rw [betheThresholdFeasibilityBudget, hRthreshold]
    simp only [pow_two]
  rw [machineOptimizerFeasibilityStateGuardSource,
    machineOptimizerFeasibilityEllipsoidDimensionUnary_encode hn,
    machineOptimizerFeasibilityInitialMagnitudeLengthRuler_encode (by omega),
    machineOptimizerFeasibilityBudgetUnary_encode hn,
    machineOptimizerFeasibilityRoundingPrecisionUnary_encode hn]
  simp only [List.length_append, List.length_replicate]
  rw [hbudget]
  omega

@[simp] theorem machineOptimizerFeasibilityStateBoundUnary_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityStateBoundUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (explicitBallFeasibilityStateCodeBound ((n - 1) ^ 2 + 1)
          (betheThresholdFeasibilityBudget (n - 1) upper.value
            (rawExplicitOptimizerInnerRadius n
              (rationalMatrixEntryBitBound A)).value)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value) true := by
  let d := (n - 1) ^ 2 + 1
  let K := explicitBallInitialMagnitudeExponent d
    (rawOptimizerFeasibilityOuterRadius n
      (rationalMatrixEntryBitBound A) upper).value
  let T := betheThresholdFeasibilityBudget (n - 1) upper.value
    (rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value
  let p := explicitBallFeasibilityPrecision d T
    (rawOptimizerFeasibilityOuterRadius n
      (rationalMatrixEntryBitBound A) upper).value
  rw [machineOptimizerFeasibilityStateBoundUnary,
    machineOptimizerFeasibilityStateBoundBits_encode (by omega)]
  apply machineBoundedUnary_encode_of_le
  rw [machineOptimizerFeasibilityStateGuard,
    machineIteratedBinaryWidth_length,
    machineOptimizerFeasibilityStateGuardSource_length_encode hn]
  simpa only [d, K, T, p, explicitBallFeasibilityStateCodeBound,
    scheduledFeasibilityStateCodeBound, explicitBallInitialDetExponent] using!
    optimizerFeasibilityStateBound_le_guardPolynomial d K T p

end BeyondBethe
