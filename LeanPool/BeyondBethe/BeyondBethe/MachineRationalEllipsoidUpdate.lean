/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalDirectionUpdateMatrix

/-!
# Polynomial-time rational central ellipsoid update

This module combines the verified center computation, the full rank-one
direction matrix, and exact matrix multiplication into the canonical code of
one complete rational ellipsoid state.
-/

namespace BeyondBethe

open Complexity

def machineRationalEllipsoidUpdateDirectionMatrixCode
    (word : List Bool) : List Bool :=
  machineRationalDirectionUpdateMatrixCode
    (pair (machineRationalCenterUpdateDimensionUnary word)
      (pair (machineRationalCenterUpdateDimensionBits word)
        (machineRationalCenterUpdatePulledBackCode word)))

def machineRationalEllipsoidUpdateBasisCode
    (word : List Bool) : List Bool :=
  machineRationalMatrixMulCode
    (pair (machineRationalCenterUpdateDimensionUnary word)
      (pair (machineRationalCenterUpdateBasisWord word)
        (machineRationalEllipsoidUpdateDirectionMatrixCode word)))

/-- Input: `pair rationalEllipsoidStateBinaryCode cutVectorCode`. -/
def machineRationalEllipsoidCentralUpdateCode
    (word : List Bool) : List Bool :=
  pair (machineRationalCenterUpdateDimensionBits word)
    (pair (machineRationalEllipsoidCenterUpdateCode word)
      (machineRationalEllipsoidUpdateBasisCode word))

theorem machineRationalEllipsoidUpdateDirectionMatrixCode_mem_FP :
    machineRationalEllipsoidUpdateDirectionMatrixCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateDimensionUnary_mem_FP
    (machinePair_mem_FP machineRationalCenterUpdateDimensionBits_mem_FP
      machineRationalCenterUpdatePulledBackCode_mem_FP)
  simpa only [machineRationalEllipsoidUpdateDirectionMatrixCode] using!
    machineCompose_mem_FP hinput
      machineRationalDirectionUpdateMatrixCode_mem_FP

theorem machineRationalEllipsoidUpdateBasisCode_mem_FP :
    machineRationalEllipsoidUpdateBasisCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateDimensionUnary_mem_FP
    (machinePair_mem_FP machineRationalCenterUpdateBasisWord_mem_FP
      machineRationalEllipsoidUpdateDirectionMatrixCode_mem_FP)
  simpa only [machineRationalEllipsoidUpdateBasisCode] using!
    machineCompose_mem_FP hinput machineRationalMatrixMulCode_mem_FP

theorem machineRationalEllipsoidCentralUpdateCode_mem_FP :
    machineRationalEllipsoidCentralUpdateCode ∈ FP := by
  exact machinePair_mem_FP machineRationalCenterUpdateDimensionBits_mem_FP
    (machinePair_mem_FP machineRationalEllipsoidCenterUpdateCode_mem_FP
      machineRationalEllipsoidUpdateBasisCode_mem_FP)

@[simp] theorem machineRationalEllipsoidUpdateDirectionMatrixCode_encode
    {d : ℕ} (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalEllipsoidUpdateDirectionMatrixCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalSquareMatrixRowsCode
        (rationalDirectionUpdateMatrix (rationalPulledBackNormal E a)) := by
  rw [machineRationalEllipsoidUpdateDirectionMatrixCode]
  simp only [machineRationalCenterUpdateDimensionUnary_encode,
    machineRationalCenterUpdateDimensionBits,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidDimensionWord_encode,
    machineRationalCenterUpdatePulledBackCode_encode]
  change machineRationalDirectionUpdateMatrixCode
      (rationalDirectionUpdateCanonicalWord
        (rationalPulledBackNormal E a)) = _
  rw [machineRationalDirectionUpdateMatrixCode_encode]

theorem rationalEllipsoidCentralUpdate_basis_eq {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    (rationalEllipsoidCentralUpdate E a).basis =
      rationalMatrixMul E.basis
        (rationalDirectionUpdateMatrix (rationalPulledBackNormal E a)) := by
  simp only [rationalEllipsoidCentralUpdate,
    rationalDirectionUpdateMatrix, rationalMatrixMul_eq_matrix_mul]

@[simp] theorem machineRationalEllipsoidUpdateBasisCode_encode
    {d : ℕ} (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalEllipsoidUpdateBasisCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalSquareMatrixRowsCode
        (rationalEllipsoidCentralUpdate E a).basis := by
  rw [machineRationalEllipsoidUpdateBasisCode]
  simp only [machineRationalCenterUpdateDimensionUnary_encode,
    machineRationalCenterUpdateBasisWord,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidBasisWord_encode,
    machineRationalEllipsoidUpdateDirectionMatrixCode_encode]
  change machineRationalMatrixMulCode
      (rationalMatrixMulCanonicalWord E.basis
        (rationalDirectionUpdateMatrix (rationalPulledBackNormal E a))) = _
  rw [machineRationalMatrixMulCode_encode,
    ← rationalEllipsoidCentralUpdate_basis_eq]

@[simp] theorem machineRationalEllipsoidCentralUpdateCode_encode
    {d : ℕ} (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalEllipsoidCentralUpdateCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalEllipsoidStateBinaryCode
        (rationalEllipsoidCentralUpdate E a) := by
  rw [machineRationalEllipsoidCentralUpdateCode,
    machineRationalEllipsoidCenterUpdateCode_encode,
    machineRationalEllipsoidUpdateBasisCode_encode]
  simp only [machineRationalCenterUpdateDimensionBits,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidDimensionWord,
    rationalEllipsoidStateBinaryCode]

end BeyondBethe
