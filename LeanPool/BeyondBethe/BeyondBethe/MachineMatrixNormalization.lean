/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalPower

/-!
# Machine normalization scale and its dimension power
-/

namespace BeyondBethe

open Complexity

def machineMatrixNormalizationScalePowerRawCode
    (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineMatrixDimensionUnary word)
      (machineMatrixNormalizationScaleRawCode word))

def machineMatrixNormalizationScalePowerOutputCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode
    (machineMatrixNormalizationScalePowerRawCode word)

theorem machineMatrixNormalizationScalePowerRawCode_mem_FP :
    machineMatrixNormalizationScalePowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixDimensionUnary_mem_FP
    machineMatrixNormalizationScaleRawCode_mem_FP
  simpa only [machineMatrixNormalizationScalePowerRawCode] using!
    machineCompose_mem_FP hpair machineRawRatPowerCode_mem_FP

theorem machineMatrixNormalizationScalePowerOutputCode_mem_FP :
    machineMatrixNormalizationScalePowerOutputCode ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizationScalePowerOutputCode] using!
    machineCompose_mem_FP
      machineMatrixNormalizationScalePowerRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

@[simp] theorem machineMatrixNormalizationScalePowerRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScalePowerRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        ((RawRat.one.add
          (rawRatRowsSum RawRat.zero (rationalMatrixRows A))).pow n) := by
  rw [machineMatrixNormalizationScalePowerRawCode,
    machineMatrixDimensionUnary_encode,
    machineMatrixNormalizationScaleRawCode_encode,
    machineRawRatPowerCode_encode]

@[simp] theorem machineMatrixNormalizationScalePowerOutputCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScalePowerOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode ((1 + ∑ i, ∑ j, A i j) ^ n) := by
  rw [machineMatrixNormalizationScalePowerOutputCode,
    machineMatrixNormalizationScalePowerRawCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_pow,
    RawRat.value_add, RawRat.value_one, rawRatRowsSum_value,
    RawRat.value_zero, zero_add, rationalMatrixRows_sum]

end BeyondBethe
