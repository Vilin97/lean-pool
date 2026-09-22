/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixNormalization
import LeanPool.BeyondBethe.BeyondBethe.MachineSmallDimension
import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly

/-!
# Connections between scalar machines and the completed algorithm
-/

namespace BeyondBethe

@[simp] theorem machineMatrixNonnegativeBit_finalDecision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNonnegativeBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [rationalMatrixNonnegativeDecision A] := by
  rw [machineMatrixNonnegativeBit_encode]
  apply congrArg singleton
  apply Bool.eq_iff_iff.mpr
  simp [rationalMatrixNonnegativeDecision, Matrix.Nonnegative]

@[simp] theorem machineMatrixNormalizationScaleOutputCode_final {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScaleOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (rationalNormalizationScale A) := by
  simpa only [rationalNormalizationScale] using!
    machineMatrixNormalizationScaleOutputCode_encode A

@[simp] theorem machineMatrixNormalizationScalePowerOutputCode_final {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizationScalePowerOutputCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (rationalNormalizationScale A ^ n) := by
  simpa only [rationalNormalizationScale] using!
    machineMatrixNormalizationScalePowerOutputCode_encode A

end BeyondBethe
