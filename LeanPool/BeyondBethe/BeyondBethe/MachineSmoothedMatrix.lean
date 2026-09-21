/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixAddDelta
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixNormalizeEntries
import LeanPool.BeyondBethe.BeyondBethe.MachineSmoothingDelta

/-!
# The complete normalization-and-smoothing matrix transform

The input is `pair chiRawCode matrixCode`.  We normalize the matrix, compute
the raw smoothing witness from that normalized matrix, and add the witness to
every normalized entry.  Keeping the smoothing witness in raw-fraction format
is essential: the canonical public rational output uses a different encoding
and cannot be fed directly to the matrix-entry arithmetic machines.
-/

namespace BeyondBethe

open Complexity

def machineSmoothedMatrixChiRawCode (word : List Bool) : List Bool :=
  machinePairFirst word

def machineSmoothedMatrixInputCode (word : List Bool) : List Bool :=
  machinePairSecond word

def machineSmoothedMatrixNormalizedCode (word : List Bool) : List Bool :=
  machineMatrixNormalizeEntries (machineSmoothedMatrixInputCode word)

def machineSmoothedMatrixDeltaRawCode (word : List Bool) : List Bool :=
  machineSmoothingDeltaRawCode
    (pair (machineSmoothedMatrixChiRawCode word)
      (machineSmoothedMatrixNormalizedCode word))

def machineSmoothedMatrixCode (word : List Bool) : List Bool :=
  machineMatrixAddDeltaEntries
    (pair (machineSmoothedMatrixDeltaRawCode word)
      (machineSmoothedMatrixNormalizedCode word))

theorem machineSmoothedMatrixChiRawCode_mem_FP :
    machineSmoothedMatrixChiRawCode ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineSmoothedMatrixInputCode_mem_FP :
    machineSmoothedMatrixInputCode ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineSmoothedMatrixNormalizedCode_mem_FP :
    machineSmoothedMatrixNormalizedCode ∈ Complexity.FP := by
  simpa only [machineSmoothedMatrixNormalizedCode] using
    machineCompose_mem_FP machineSmoothedMatrixInputCode_mem_FP
      machineMatrixNormalizeEntries_mem_FP

theorem machineSmoothedMatrixDeltaRawCode_mem_FP :
    machineSmoothedMatrixDeltaRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSmoothedMatrixChiRawCode_mem_FP
    machineSmoothedMatrixNormalizedCode_mem_FP
  simpa only [machineSmoothedMatrixDeltaRawCode] using
    machineCompose_mem_FP hpair machineSmoothingDeltaRawCode_mem_FP

theorem machineSmoothedMatrixCode_mem_FP :
    machineSmoothedMatrixCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSmoothedMatrixDeltaRawCode_mem_FP
    machineSmoothedMatrixNormalizedCode_mem_FP
  simpa only [machineSmoothedMatrixCode] using
    machineCompose_mem_FP hpair machineMatrixAddDeltaEntries_mem_FP

@[simp] theorem machineSmoothedMatrixNormalizedCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothedMatrixNormalizedCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, normalizedRationalMatrix A⟩ := by
  simp [machineSmoothedMatrixNormalizedCode,
    machineSmoothedMatrixInputCode]

@[simp] theorem machineSmoothedMatrixDeltaRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothedMatrixDeltaRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode
        (rawRationalSmoothingDelta (normalizedRationalMatrix A) χ) := by
  simp [machineSmoothedMatrixDeltaRawCode,
    machineSmoothedMatrixChiRawCode]

@[simp] theorem machineSmoothedMatrixCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothedMatrixCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, smoothedRationalMatrix A χ.value⟩ := by
  rw [machineSmoothedMatrixCode,
    machineSmoothedMatrixDeltaRawCode_encode,
    machineSmoothedMatrixNormalizedCode_encode]
  change machineMatrixAddDeltaEntries
      (machineMatrixAddDeltaCanonicalInput
        (rawRationalSmoothingDelta (normalizedRationalMatrix A) χ)
        (normalizedRationalMatrix A)) = _
  rw [machineMatrixAddDeltaEntries_encode]
  congr 2
  funext i j
  simp only [rationalMatrixAddDeltaSemantic, smoothedRationalMatrix]
  rw [rawRationalSmoothingDelta_value]

@[simp] theorem machineSmoothedMatrixCode_rational {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ) :
    machineSmoothedMatrixCode
        (pair (rawRatBinaryCode (rawRatOfRat χ))
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, smoothedRationalMatrix A χ⟩ := by
  rw [machineSmoothedMatrixCode_encode, rawRatOfRat_value]

end BeyondBethe
