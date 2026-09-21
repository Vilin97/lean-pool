/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RawRational
import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryMul
import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryCompare
import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryDivision
import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryGCD
import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerArithmetic
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalization
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalArithmetic
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalUnary
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare
import LeanPool.BeyondBethe.BeyondBethe.MachineDyadicFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalLogSeries
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalExp
import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedLog
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixNonnegative
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMin
import LeanPool.BeyondBethe.BeyondBethe.MachineFactorial
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalRowAdd
import LeanPool.BeyondBethe.BeyondBethe.MachineNearbyCoordinate

/-! # Machine Arithmetic Tests -/

namespace BeyondBethe

/-! Exhaustive executable smoke tests for the machine-arithmetic core. -/

theorem binaryLongDiv_exhaustive_256_by_64 :
    ∀ a : Fin 256, ∀ b : Fin 64,
      binaryLongDiv a.val b.val = (a.val / b.val, a.val % b.val) := by
  native_decide

theorem binaryEuclidBounded_exhaustive_128_by_128 :
    ∀ a : Fin 128, ∀ b : Fin 128,
      binaryEuclidBounded a.val b.val = Nat.gcd a.val b.val := by
  native_decide

theorem machineBinaryMul_exhaustive_64_by_64 :
    ∀ a : Fin 64, ∀ b : Fin 64,
      machineBinaryMulBits (Complexity.pair a.val.bits b.val.bits) =
        (a.val * b.val).bits := by
  native_decide

theorem machineBinarySub_exhaustive_64_by_64 :
    ∀ a : Fin 64, ∀ b : Fin 64,
      machineBinarySubBits (Complexity.pair a.val.bits b.val.bits) =
        (a.val - b.val).bits := by
  native_decide

theorem machineBinaryCompare_exhaustive_64_by_64 :
    ∀ a : Fin 64, ∀ b : Fin 64,
      machineBinaryNatLeBit (Complexity.pair a.val.bits b.val.bits) =
          [decide (a.val ≤ b.val)] ∧
      machineBinaryNatLtBit (Complexity.pair a.val.bits b.val.bits) =
          [decide (a.val < b.val)] ∧
      machineBinaryNatEqBit (Complexity.pair a.val.bits b.val.bits) =
          [decide (a.val = b.val)] := by
  native_decide

theorem machineBinaryDivision_exhaustive_64_by_32 :
    ∀ a : Fin 64, ∀ b : Fin 32,
      machineBinaryDivModBits (Complexity.pair a.val.bits b.val.bits) =
        Complexity.pair (a.val / b.val).bits (a.val % b.val).bits := by
  native_decide

theorem machineBinaryGcd_exhaustive_32_by_32 :
    ∀ a : Fin 32, ∀ b : Fin 32,
      machineBinaryGcdBits (Complexity.pair a.val.bits b.val.bits) =
        (Nat.gcd a.val b.val).bits := by
  native_decide

def signedIntegerTest (negative : Bool) (n : ℕ) : ℤ :=
  if negative then Int.negSucc n else Int.ofNat n

theorem machineIntegerArithmetic_exhaustive_signed_16 :
    ∀ leftNegative rightNegative : Bool, ∀ a b : Fin 16,
      machineIntegerAddCode
          (Complexity.pair
            (integerBinaryCode (signedIntegerTest leftNegative a.val))
            (integerBinaryCode (signedIntegerTest rightNegative b.val))) =
        integerBinaryCode
          (signedIntegerTest leftNegative a.val +
            signedIntegerTest rightNegative b.val) ∧
      machineIntegerMulCode
          (Complexity.pair
            (integerBinaryCode (signedIntegerTest leftNegative a.val))
            (integerBinaryCode (signedIntegerTest rightNegative b.val))) =
        integerBinaryCode
          (signedIntegerTest leftNegative a.val *
            signedIntegerTest rightNegative b.val) ∧
      machineIntegerNegCode
          (integerBinaryCode (signedIntegerTest leftNegative a.val)) =
        integerBinaryCode (-signedIntegerTest leftNegative a.val) := by
  native_decide

def positiveRawRatTest (n d : ℕ) : RawRat :=
  ⟨Int.ofNat n, d + 1, by omega⟩

def negativeRawRatTest (n d : ℕ) : RawRat :=
  ⟨Int.negSucc n, d + 1, by omega⟩

def signedRawRatTest (negative : Bool) (n d : ℕ) : RawRat :=
  if negative then negativeRawRatTest n d else positiveRawRatTest n d

theorem machineRationalNormalization_exhaustive_signed_8_by_8 :
    ∀ n : Fin 8, ∀ d : Fin 8,
      machineNormalizeRawRatBinaryCode
          (rawRatBinaryCode (positiveRawRatTest n.val d.val)) =
        rationalBinaryCode
          (binaryNormalizeRawRat (positiveRawRatTest n.val d.val)) ∧
      machineNormalizeRawRatBinaryCode
          (rawRatBinaryCode (negativeRawRatTest n.val d.val)) =
        rationalBinaryCode
          (binaryNormalizeRawRat (negativeRawRatTest n.val d.val)) := by
  native_decide

theorem machineRationalArithmetic_exhaustive_signed_3 :
    ∀ leftNegative rightNegative : Bool,
      ∀ leftNum leftDen rightNum rightDen : Fin 3,
      let q := signedRawRatTest leftNegative leftNum.val leftDen.val
      let r := signedRawRatTest rightNegative rightNum.val rightDen.val
      machineRationalAddCode
          (Complexity.pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
        rationalBinaryCode (binaryNormalizeRawRat (q.add r)) ∧
      machineRationalMulCode
          (Complexity.pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
        rationalBinaryCode (binaryNormalizeRawRat (q.mul r)) := by
  native_decide

theorem machineRationalComparison_exhaustive_signed_4 :
    ∀ leftNegative rightNegative : Bool,
      ∀ leftNum leftDen rightNum rightDen : Fin 4,
      let q := signedRawRatTest leftNegative leftNum.val leftDen.val
      let r := signedRawRatTest rightNegative rightNum.val rightDen.val
      machineRawRatLeBit
          (Complexity.pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
        [decide (q.value ≤ r.value)] := by
  native_decide

theorem machineRationalUnary_exhaustive_signed_3 :
    ∀ leftNegative rightNegative : Bool,
      ∀ leftNum leftDen rightNum rightDen : Fin 3,
      let q := signedRawRatTest leftNegative leftNum.val leftDen.val
      let r := signedRawRatTest rightNegative rightNum.val rightDen.val
      machineRationalNegCode (rawRatBinaryCode q) =
          rationalBinaryCode (binaryNormalizeRawRat q.neg) ∧
      machineRationalInvCode (rawRatBinaryCode q) =
          rationalBinaryCode (binaryNormalizeRawRat q.inv) ∧
      machineRationalDivCode
          (Complexity.pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
        rationalBinaryCode (binaryNormalizeRawRat (q.div r)) := by
  native_decide

theorem machineDyadicFloor_exhaustive_signed_4 :
    ∀ negative : Bool, ∀ p n d : Fin 4,
      let q := signedRawRatTest negative n.val d.val
      machineDyadicFloorCode
          (Complexity.pair (List.replicate p.val true)
            (rawRatBinaryCode q)) =
      rationalBinaryCode (binaryDyadicFloor p.val q.value) := by
  native_decide

theorem machineRationalFloorCeil_exhaustive_signed_8 :
    ∀ negative : Bool, ∀ n : Fin 8, ∀ d : Fin 8,
      let q := signedRawRatTest negative n.val d.val
      machineRationalFloorIntegerCode (rawRatBinaryCode q) =
          integerBinaryCode (binaryRatFloor q.value) ∧
        machineRationalCeilIntegerCode (rawRatBinaryCode q) =
          integerBinaryCode (binaryRatCeil q.value) ∧
        machineRationalCeilNatBits (rawRatBinaryCode q) =
          (Int.toNat (binaryRatCeil q.value)).bits := by
  native_decide

theorem machineRationalLogSeriesSum_exhaustive_signed_3 :
    ∀ negative : Bool, ∀ n : Fin 3, ∀ d : Fin 3, ∀ N : Fin 3,
      let q := signedRawRatTest negative n.val d.val
      machineRationalLogSeriesSumCode
          (Complexity.pair (List.replicate N.val true)
            (rawRatBinaryCode q)) =
        rationalBinaryCode (binaryRationalLogSeriesSum q.value N.val) := by
  native_decide

theorem machineBoundedUnary_exhaustive_8 :
    ∀ guard n : Fin 8,
      machineBoundedUnary
          (Complexity.pair (List.replicate guard.val true) n.val.bits) =
        List.replicate (min guard.val n.val) true := by
  native_decide

theorem machineBoundedRationalExpLower_small_signed :
    ∀ negative : Bool, ∀ n d : Fin 2,
      let s := signedRawRatTest negative n.val d.val
      let M := RawRat.expApproxSteps s RawRat.one
      machineBoundedRationalExpLowerCode
          (Complexity.pair (List.replicate M true)
            (Complexity.pair (rawRatBinaryCode s)
              (rawRatBinaryCode RawRat.one))) =
        rationalBinaryCode
          (binaryRationalExpLower s.value RawRat.one.value) := by
  native_decide

theorem machineLengthBits_exhaustive_16 :
    ∀ n : Fin 16,
      machineLengthBits (List.replicate n.val true) = n.val.bits := by
  native_decide

def positiveNonzeroRawRatTest (n d : ℕ) : RawRat :=
  ⟨Int.ofNat (n + 1), d + 1, by omega⟩

theorem machineDirectedLog_small_positive :
    ∀ n d N : Fin 2,
      let q := (positiveNonzeroRawRatTest n.val d.val).value
      machineDirectedLogLowerCode
          (Complexity.pair (List.replicate N.val true)
            (rawRatBinaryCode (rawRatOfRat q))) =
          rationalBinaryCode (binaryDirectedLogLower q N.val) ∧
        machineDirectedLogUpperCode
          (Complexity.pair (List.replicate N.val true)
            (rawRatBinaryCode (rawRatOfRat q))) =
          rationalBinaryCode (binaryDirectedLogUpper q N.val) := by
  intro n d N
  dsimp only
  exact ⟨machineDirectedLogLowerCode_encode _ _,
    machineDirectedLogUpperCode_encode _ _⟩

theorem machineMatrixNonnegative_two_by_two :
    ∀ negative : Bool,
      let A : Matrix (Fin 2) (Fin 2) ℚ := fun i j ↦
        if negative && decide (i = 0) && decide (j = 0) then -1 else 1
      machineMatrixNonnegativeBit
          (rationalMatrixBinaryEncoding.encode ⟨2, A⟩) =
        [!negative] := by
  native_decide

theorem machineMatrixSum_two_by_two_constant :
    ∀ q : Fin 3,
      let A : Matrix (Fin 2) (Fin 2) ℚ := fun _ _ ↦ q.val
      machineMatrixSumOutputCode
          (rationalMatrixBinaryEncoding.encode ⟨2, A⟩) =
        rationalBinaryCode (4 * q.val) := by
  native_decide

theorem machineRationalMin_exhaustive_positive_3 :
    ∀ leftNum leftDen rightNum rightDen : Fin 3,
      let q := positiveRawRatTest leftNum.val leftDen.val
      let r := positiveRawRatTest rightNum.val rightDen.val
      machineRationalMinCode
          (Complexity.pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
        rationalBinaryCode (min q.value r.value) := by
  native_decide

theorem machineFactorial_exhaustive_8 :
    ∀ n : Fin 8,
      machineFactorialRawRatCode (List.replicate n.val true) =
        rawRatBinaryCode (RawRat.ofNat n.val.factorial) := by
  native_decide

theorem machineRationalRowAdd_exhaustive_2 :
    ∀ deltaNum deltaDen left right : Fin 2,
      let delta := positiveRawRatTest deltaNum.val deltaDen.val
      let row : List ℚ := [left.val, right.val]
      machineRationalRowAdd
          (machineRationalRowAddCanonicalInput delta row) =
        binaryListCode rationalEntryBinaryCode
          (rationalRowAddValues delta row) := by
  native_decide

theorem machineScheduledLogTermsRuler_three_halves :
    machineScheduledLogTermsRuler
        (Complexity.pair (List.replicate 3 true)
          (rawRatBinaryCode (rawRatOfRat (3 / 2 : ℚ)))) =
      List.replicate (directedLogTerms (3 / 2 : ℚ) 3) true := by
  native_decide

theorem machineNearbyCoordinate_one_third :
    let tau := rawRatOfRat (1 / 4 : ℚ)
    machineNearbyCoordinateLowerRawCode
        (Complexity.pair (List.replicate 3 true)
          (Complexity.pair (rawRatBinaryCode tau)
            (rationalEntryBinaryCode (1 / 3 : ℚ)))) =
      rawRatBinaryCode (rawNearbyCoordinateLower tau (1 / 3 : ℚ) 3) := by
  exact machineNearbyCoordinateLowerRawCode_encode _ _ _

end BeyondBethe
