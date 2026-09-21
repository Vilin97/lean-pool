/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorScan
import LeanPool.BeyondBethe.BeyondBethe.MachineExecutableScannedOptimizerOutput
import LeanPool.BeyondBethe.BeyondBethe.MachineMatchingGain

/-!
# Exhaustive small tests for the optimizer and certificate boundary

These tests are deliberately separate from the production dependency graph.
They execute the finite-word programs on small finite families; correctness of
the public theorem itself continues to use the symbolic proofs.
-/

namespace BeyondBethe

open Complexity

def optimizerTestAffinePoint {N : ℕ} (a : Fin N) : Fin 1 → ℚ :=
  fun _ ↦ a.val / 4

def optimizerTestFloor {N : ℕ} (d : Fin N) : RawRat :=
  rawRatOfRat (d.val / 4 : ℚ)

theorem machineBetheFloorViolation_exhaustive_two_by_two_quarters :
    ∀ a d : Fin 2, ∀ i j : Fin 2,
      machineBetheFloorViolationBit
          (machineBetheFloorTestCanonicalWord
            (optimizerTestFloor d) i j (optimizerTestAffinePoint a)) =
        [decide (betheAffineMatrixQ (optimizerTestAffinePoint a) i j <
          (optimizerTestFloor d).value)] := by
  native_decide

theorem machineBetheFloorScan_exhaustive_two_by_two_quarters :
    ∀ a d : Fin 3,
      machineBetheFloorScanResultCode
          (machineBetheFloorScanCanonicalWord (m := 1)
            (optimizerTestFloor d) (optimizerTestAffinePoint a)) =
        betheFloorScanSemanticResultCode
          (finalBetheFloorScanSemanticState (m := 1)
            (optimizerTestFloor d) (optimizerTestAffinePoint a)) := by
  native_decide

theorem machineExecutableMatrixEntry_exhaustive_two_by_two_quarters :
    ∀ a : Fin 3, ∀ i j : Fin 2,
      let y : Fin 1 → ℚ := fun _ ↦ a.val / 4
      machineExecutableMatrixEntryCode
          (pair (List.replicate i.1 true)
            (pair (List.replicate j.1 true)
              (pair [true] (rationalFiniteVectorCode y)))) =
        rationalEntryBinaryCode (betheAffineMatrixQ y i j) := by
  native_decide

theorem machineExecutablePotentialEntries_two_by_two_half :
    let A : Matrix (Fin 2) (Fin 2) ℚ := fun _ _ ↦ 1
    let y : Fin 1 → ℚ := fun _ ↦ 1 / 2
    ∀ dummy i : Fin 2,
      machineExecutableRowPotentialEntryCode
          (pair (List.replicate dummy.1 true)
            (pair (List.replicate i.1 true)
              (machineDirectedObjectiveSumCanonicalWord (1 / 8) A y 1))) =
        rationalEntryBinaryCode
          (-directedNegativeGradientLowerMatrix (1 / 8) A
              (betheAffineMatrixQ y) 1 i 0 + (2 + 1 / 8)) ∧
      machineExecutableColumnPotentialEntryCode
          (pair (List.replicate dummy.1 true)
            (pair (List.replicate i.1 true)
              (machineDirectedObjectiveSumCanonicalWord (1 / 8) A y 1))) =
        rationalEntryBinaryCode
          (-(directedNegativeGradientLowerMatrix (1 / 8) A
              (betheAffineMatrixQ y) 1 0 i -
            directedNegativeGradientLowerMatrix (1 / 8) A
              (betheAffineMatrixQ y) 1 0 0)) := by
  dsimp only
  intro dummy i
  exact ⟨
    machineExecutableRowPotentialEntryCode_encode
      (1 / 8) (fun _ _ ↦ 1) (fun _ ↦ 1 / 2) 1 dummy i,
    machineExecutableColumnPotentialEntryCode_encode
      (1 / 8) (fun _ _ ↦ 1) (fun _ ↦ 1 / 2) 1 dummy i⟩

def optimizerTestEntry (bit : Bool) : ℚ :=
  if bit then 3 / 4 else 1 / 4

theorem machineMatchingGain_exhaustive_two_by_two_binary_entries :
    ∀ a b c d : Bool,
      let X : Matrix (Fin 2) (Fin 2) ℚ := fun i j ↦
        if i = 0 then
          if j = 0 then optimizerTestEntry a else optimizerTestEntry b
        else if j = 0 then optimizerTestEntry c else optimizerTestEntry d
      let R : Fin 2 → ℚ := fun _ ↦ 0
      let C : Fin 2 → ℚ := fun _ ↦ 0
      machineExplicitMatchingGainRawCode
          (pair [] (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
        rawRatBinaryCode (rawRatOfRat (explicitCertifiedMatchingGain X)) := by
  intro a b c d
  dsimp only
  exact machineExplicitMatchingGainRawCode_encode []
    (fun i j ↦
      if i = 0 then
        if j = 0 then optimizerTestEntry a else optimizerTestEntry b
      else if j = 0 then optimizerTestEntry c else optimizerTestEntry d)
    (fun _ ↦ 0) (fun _ ↦ 0)

end BeyondBethe
