/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeGradientCoordinate
public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeObjectiveSum

/-!
# Finite-word entries of the directed full gradient

The adapter in this file adds a queried row and column to the canonical
directed-objective payload.  It then reuses the already verified matrix-entry
and affine-entry recovery path of the row-major objective machine and sends
the resulting scalar input to the directed gradient machine.  This keeps the
objective and gradient implementations on one common interpretation of `A`
and of the recovered Birkhoff matrix.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary row index from a negative-gradient entry query. -/
def machineDirectedGradientEntryRow (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the column index and payload from a negative-gradient entry query. -/
def machineDirectedGradientEntryRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extracts the unary column index from a negative-gradient entry query. -/
def machineDirectedGradientEntryColumn (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedGradientEntryRest word)

/-- Extracts the encoded objective payload following the row and column of a gradient-entry
request. -/
def machineDirectedGradientEntryPayload (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedGradientEntryRest word)

/-- Builds an objective-sum state for the requested gradient entry, with zero accumulator, empty
bound word, and an unset completion bit. -/
def machineDirectedGradientEntryAsObjectiveState
    (word : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack
    (machineDirectedGradientEntryRow word)
    (machineDirectedGradientEntryColumn word)
    (rawRatBinaryCode RawRat.zero) [] [false]
    (machineDirectedGradientEntryPayload word)

/-- Assembles precision, regularization parameter, matrix entry, and affine entry for the
requested gradient coordinate. -/
def machineDirectedGradientEntryScalarInput
    (word : List Bool) : List Bool :=
  machineDirectedObjectiveSumCoordinateInput
    (machineDirectedGradientEntryAsObjectiveState word)

/-- Computes the encoded directed lower approximation to the negative gradient at the requested
matrix entry. -/
def machineDirectedNegativeGradientEntryRawCode
    (word : List Bool) : List Bool :=
  machineDirectedNegativeGradientLowerRawCode
    (machineDirectedGradientEntryScalarInput word)

theorem machineDirectedGradientEntryRow_mem_FP :
    machineDirectedGradientEntryRow ∈ FP := machinePairFirst_mem_FP

theorem machineDirectedGradientEntryRest_mem_FP :
    machineDirectedGradientEntryRest ∈ FP := machinePairSecond_mem_FP

theorem machineDirectedGradientEntryColumn_mem_FP :
    machineDirectedGradientEntryColumn ∈ FP := by
  simpa only [machineDirectedGradientEntryColumn] using!
    machineCompose_mem_FP machineDirectedGradientEntryRest_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedGradientEntryPayload_mem_FP :
    machineDirectedGradientEntryPayload ∈ FP := by
  simpa only [machineDirectedGradientEntryPayload] using!
    machineCompose_mem_FP machineDirectedGradientEntryRest_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedGradientEntryAsObjectiveState_mem_FP :
    machineDirectedGradientEntryAsObjectiveState ∈ FP := by
  have hacc : (fun _ : List Bool => rawRatBinaryCode RawRat.zero) ∈ FP :=
    machineConst_mem_FP _
  have hbound : (fun _ : List Bool => ([] : List Bool)) ∈ FP :=
    machineConst_mem_FP _
  have hdone : (fun _ : List Bool => [false]) ∈ FP :=
    machineConst_mem_FP _
  have htail := machinePair_mem_FP hdone
    machineDirectedGradientEntryPayload_mem_FP
  have hwithBound := machinePair_mem_FP hbound htail
  have hwithAcc := machinePair_mem_FP hacc hwithBound
  have hwithColumn := machinePair_mem_FP
    machineDirectedGradientEntryColumn_mem_FP hwithAcc
  simpa only [machineDirectedGradientEntryAsObjectiveState,
    machineDirectedObjectiveSumPack] using!
    machinePair_mem_FP machineDirectedGradientEntryRow_mem_FP hwithColumn

theorem machineDirectedGradientEntryScalarInput_mem_FP :
    machineDirectedGradientEntryScalarInput ∈ FP := by
  simpa only [machineDirectedGradientEntryScalarInput] using!
    machineCompose_mem_FP
      machineDirectedGradientEntryAsObjectiveState_mem_FP
      machineDirectedObjectiveSumCoordinateInput_mem_FP

theorem machineDirectedNegativeGradientEntryRawCode_mem_FP :
    machineDirectedNegativeGradientEntryRawCode ∈ FP := by
  simpa only [machineDirectedNegativeGradientEntryRawCode] using!
    machineCompose_mem_FP machineDirectedGradientEntryScalarInput_mem_FP
      machineDirectedNegativeGradientLowerRawCode_mem_FP

/-- Encodes row and column as unary rulers preceding the canonical objective payload for `tau`,
`A`, `y`, and precision `p`. -/
def machineDirectedGradientEntryCanonicalWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) : List Bool :=
  pair (List.replicate i.1 true)
    (pair (List.replicate j.1 true)
      (machineDirectedObjectiveSumCanonicalWord tau A y p))

@[simp] theorem machineDirectedGradientEntryAsObjectiveState_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    machineDirectedGradientEntryAsObjectiveState
        (machineDirectedGradientEntryCanonicalWord tau A y p i j) =
      machineDirectedObjectiveSumCanonicalState tau A y p i j
        RawRat.zero false [] := by
  simp [machineDirectedGradientEntryAsObjectiveState,
    machineDirectedGradientEntryCanonicalWord,
    machineDirectedGradientEntryRow,
    machineDirectedGradientEntryColumn,
    machineDirectedGradientEntryRest,
    machineDirectedGradientEntryPayload,
    machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedGradientEntryScalarInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    machineDirectedGradientEntryScalarInput
        (machineDirectedGradientEntryCanonicalWord tau A y p i j) =
      machineDirectedObjectiveCoordinateCanonicalWord tau (A i j)
        (betheAffineMatrixQ y i j) p := by
  rw [machineDirectedGradientEntryScalarInput,
    machineDirectedGradientEntryAsObjectiveState_encode,
    machineDirectedObjectiveSumCoordinateInput_canonicalState]

@[simp] theorem machineDirectedNegativeGradientEntryRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    machineDirectedNegativeGradientEntryRawCode
        (machineDirectedGradientEntryCanonicalWord tau A y p i j) =
      rawRatBinaryCode
        (rawDirectedNegativeGradientLower tau (A i j)
          (betheAffineMatrixQ y i j) p) := by
  rw [machineDirectedNegativeGradientEntryRawCode,
    machineDirectedGradientEntryScalarInput_encode,
    machineDirectedNegativeGradientLowerRawCode_encode]

theorem machineDirectedNegativeGradientEntry_value {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    (rawDirectedNegativeGradientLower tau (A i j)
      (betheAffineMatrixQ y i j) p).value =
        directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p i j := by
  rw [rawDirectedNegativeGradientLower_value]
  rfl

end BeyondBethe
