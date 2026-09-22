/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedAffineGradientVector
import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryListSnoc

/-!
# Finite-word directed epigraph normals

The nonlinear oracle returns the affine-gradient vector followed by the
height coefficient `-1`.  This file performs that final append explicitly
and identifies the result with the canonical code of `epigraphNormal`.
-/

namespace BeyondBethe

open Complexity

def machineDirectedEpigraphNormalSnocInput
    (word : List Bool) : List Bool :=
  pair (rationalEntryBinaryCode (-1))
    (machineDirectedAffineGradientVectorCode word)

def machineDirectedEpigraphNormalVectorCode
    (word : List Bool) : List Bool :=
  machineBinaryListSnoc (machineDirectedEpigraphNormalSnocInput word)

theorem machineDirectedEpigraphNormalSnocInput_mem_FP :
    machineDirectedEpigraphNormalSnocInput ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP (rationalEntryBinaryCode (-1)))
    machineDirectedAffineGradientVectorCode_mem_FP

theorem machineDirectedEpigraphNormalVectorCode_mem_FP :
    machineDirectedEpigraphNormalVectorCode ∈ FP := by
  simpa only [machineDirectedEpigraphNormalVectorCode] using!
    machineCompose_mem_FP machineDirectedEpigraphNormalSnocInput_mem_FP
      machineBinaryListSnoc_mem_FP

theorem ofFn_directedEpigraphNormal {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    List.ofFn
        (epigraphNormal (directedAffineGradientVector tau A y p)) =
      List.ofFn (directedAffineGradientVector tau A y p) ++ [-1] := by
  rw [List.ofFn_succ']
  simp [epigraphNormal]

@[simp] theorem machineDirectedEpigraphNormalVectorCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedEpigraphNormalVectorCode
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rationalFiniteVectorCode
        (epigraphNormal (directedAffineGradientVector tau A y p)) := by
  rw [machineDirectedEpigraphNormalVectorCode,
    machineDirectedEpigraphNormalSnocInput,
    machineDirectedAffineGradientVectorCode_encode]
  change machineBinaryListSnoc
      (pair (rationalEntryBinaryCode (-1))
        (binaryListCode rationalEntryBinaryCode
          (List.ofFn (directedAffineGradientVector tau A y p)))) =
    binaryListCode rationalEntryBinaryCode
      (List.ofFn
        (epigraphNormal (directedAffineGradientVector tau A y p)))
  rw [machineBinaryListSnoc_encode, ofFn_directedEpigraphNormal]

@[simp] theorem machineDirectedEpigraphNormalVectorCode_encode_oracleNormal
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedEpigraphNormalVectorCode
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rationalFiniteVectorCode
        (epigraphNormal ((betheDirectedEpigraphData tau A p).gradient y)) := by
  simpa only [betheDirectedEpigraphData, directedAffineGradientVector] using!
    machineDirectedEpigraphNormalVectorCode_encode tau A y p

end BeyondBethe
