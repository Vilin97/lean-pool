/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeGradientEntry

/-!
# Finite-word entries of the directed affine gradient

For an upper-left base coordinate `(a,b)`, the affine pullback is the signed
four-corner combination

`G(a,b) - G(a,last) - G(last,b) + G(last,last)`.

This file evaluates those four full-gradient entries with the common verified
entry machine and performs the three exact rational operations explicitly.
-/

namespace BeyondBethe

open Complexity

def machineDirectedAffineGradientEntryRow
    (word : List Bool) : List Bool := machinePairFirst word

def machineDirectedAffineGradientEntryRest
    (word : List Bool) : List Bool := machinePairSecond word

def machineDirectedAffineGradientEntryColumn
    (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedAffineGradientEntryRest word)

def machineDirectedAffineGradientEntryPayload
    (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedAffineGradientEntryRest word)

def machineDirectedAffineGradientEntryDimension
    (word : List Bool) : List Bool :=
  machineDirectedObjectiveSumDimension
    (machineDirectedAffineGradientEntryPayload word)

def machineDirectedAffineGradientUpperLeftInput
    (word : List Bool) : List Bool := word

def machineDirectedAffineGradientUpperRightInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedAffineGradientEntryRow word)
    (pair (machineDirectedAffineGradientEntryDimension word)
      (machineDirectedAffineGradientEntryPayload word))

def machineDirectedAffineGradientLowerLeftInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedAffineGradientEntryDimension word)
    (pair (machineDirectedAffineGradientEntryColumn word)
      (machineDirectedAffineGradientEntryPayload word))

def machineDirectedAffineGradientLowerRightInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedAffineGradientEntryDimension word)
    (pair (machineDirectedAffineGradientEntryDimension word)
      (machineDirectedAffineGradientEntryPayload word))

def machineDirectedAffineGradientUpperLeftRaw
    (word : List Bool) : List Bool :=
  machineDirectedNegativeGradientEntryRawCode
    (machineDirectedAffineGradientUpperLeftInput word)

def machineDirectedAffineGradientUpperRightRaw
    (word : List Bool) : List Bool :=
  machineDirectedNegativeGradientEntryRawCode
    (machineDirectedAffineGradientUpperRightInput word)

def machineDirectedAffineGradientLowerLeftRaw
    (word : List Bool) : List Bool :=
  machineDirectedNegativeGradientEntryRawCode
    (machineDirectedAffineGradientLowerLeftInput word)

def machineDirectedAffineGradientLowerRightRaw
    (word : List Bool) : List Bool :=
  machineDirectedNegativeGradientEntryRawCode
    (machineDirectedAffineGradientLowerRightInput word)

def machineDirectedAffineGradientFirstDifference
    (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (machineDirectedAffineGradientUpperLeftRaw word)
      (machineDirectedAffineGradientUpperRightRaw word))

def machineDirectedAffineGradientSecondDifference
    (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (machineDirectedAffineGradientFirstDifference word)
      (machineDirectedAffineGradientLowerLeftRaw word))

def machineDirectedAffineGradientEntryRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedAffineGradientSecondDifference word)
      (machineDirectedAffineGradientLowerRightRaw word))

theorem machineDirectedAffineGradientEntryRow_mem_FP :
    machineDirectedAffineGradientEntryRow ∈ FP := machinePairFirst_mem_FP

theorem machineDirectedAffineGradientEntryRest_mem_FP :
    machineDirectedAffineGradientEntryRest ∈ FP := machinePairSecond_mem_FP

theorem machineDirectedAffineGradientEntryColumn_mem_FP :
    machineDirectedAffineGradientEntryColumn ∈ FP := by
  simpa only [machineDirectedAffineGradientEntryColumn] using!
    machineCompose_mem_FP machineDirectedAffineGradientEntryRest_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedAffineGradientEntryPayload_mem_FP :
    machineDirectedAffineGradientEntryPayload ∈ FP := by
  simpa only [machineDirectedAffineGradientEntryPayload] using!
    machineCompose_mem_FP machineDirectedAffineGradientEntryRest_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedAffineGradientEntryDimension_mem_FP :
    machineDirectedAffineGradientEntryDimension ∈ FP := by
  simpa only [machineDirectedAffineGradientEntryDimension] using!
    machineCompose_mem_FP machineDirectedAffineGradientEntryPayload_mem_FP
      machineDirectedObjectiveSumDimension_mem_FP

theorem machineDirectedAffineGradientUpperLeftInput_mem_FP :
    machineDirectedAffineGradientUpperLeftInput ∈ FP := by
  simpa only [machineDirectedAffineGradientUpperLeftInput] using!
    (Complexity.id_mem_FP : (fun x : List Bool => x) ∈ FP)

theorem machineDirectedAffineGradientUpperRightInput_mem_FP :
    machineDirectedAffineGradientUpperRightInput ∈ FP :=
  machinePair_mem_FP machineDirectedAffineGradientEntryRow_mem_FP
    (machinePair_mem_FP machineDirectedAffineGradientEntryDimension_mem_FP
      machineDirectedAffineGradientEntryPayload_mem_FP)

theorem machineDirectedAffineGradientLowerLeftInput_mem_FP :
    machineDirectedAffineGradientLowerLeftInput ∈ FP :=
  machinePair_mem_FP machineDirectedAffineGradientEntryDimension_mem_FP
    (machinePair_mem_FP machineDirectedAffineGradientEntryColumn_mem_FP
      machineDirectedAffineGradientEntryPayload_mem_FP)

theorem machineDirectedAffineGradientLowerRightInput_mem_FP :
    machineDirectedAffineGradientLowerRightInput ∈ FP :=
  machinePair_mem_FP machineDirectedAffineGradientEntryDimension_mem_FP
    (machinePair_mem_FP machineDirectedAffineGradientEntryDimension_mem_FP
      machineDirectedAffineGradientEntryPayload_mem_FP)

theorem machineDirectedAffineGradientUpperLeftRaw_mem_FP :
    machineDirectedAffineGradientUpperLeftRaw ∈ FP := by
  simpa only [machineDirectedAffineGradientUpperLeftRaw] using!
    machineCompose_mem_FP machineDirectedAffineGradientUpperLeftInput_mem_FP
      machineDirectedNegativeGradientEntryRawCode_mem_FP

theorem machineDirectedAffineGradientUpperRightRaw_mem_FP :
    machineDirectedAffineGradientUpperRightRaw ∈ FP := by
  simpa only [machineDirectedAffineGradientUpperRightRaw] using!
    machineCompose_mem_FP machineDirectedAffineGradientUpperRightInput_mem_FP
      machineDirectedNegativeGradientEntryRawCode_mem_FP

theorem machineDirectedAffineGradientLowerLeftRaw_mem_FP :
    machineDirectedAffineGradientLowerLeftRaw ∈ FP := by
  simpa only [machineDirectedAffineGradientLowerLeftRaw] using!
    machineCompose_mem_FP machineDirectedAffineGradientLowerLeftInput_mem_FP
      machineDirectedNegativeGradientEntryRawCode_mem_FP

theorem machineDirectedAffineGradientLowerRightRaw_mem_FP :
    machineDirectedAffineGradientLowerRightRaw ∈ FP := by
  simpa only [machineDirectedAffineGradientLowerRightRaw] using!
    machineCompose_mem_FP machineDirectedAffineGradientLowerRightInput_mem_FP
      machineDirectedNegativeGradientEntryRawCode_mem_FP

theorem machineDirectedAffineGradientFirstDifference_mem_FP :
    machineDirectedAffineGradientFirstDifference ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedAffineGradientUpperLeftRaw_mem_FP
    machineDirectedAffineGradientUpperRightRaw_mem_FP
  simpa only [machineDirectedAffineGradientFirstDifference] using!
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineDirectedAffineGradientSecondDifference_mem_FP :
    machineDirectedAffineGradientSecondDifference ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedAffineGradientFirstDifference_mem_FP
    machineDirectedAffineGradientLowerLeftRaw_mem_FP
  simpa only [machineDirectedAffineGradientSecondDifference] using!
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineDirectedAffineGradientEntryRawCode_mem_FP :
    machineDirectedAffineGradientEntryRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedAffineGradientSecondDifference_mem_FP
    machineDirectedAffineGradientLowerRightRaw_mem_FP
  simpa only [machineDirectedAffineGradientEntryRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

def machineDirectedAffineGradientEntryCanonicalWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) : List Bool :=
  pair (List.replicate a.1 true)
    (pair (List.replicate b.1 true)
      (machineDirectedObjectiveSumCanonicalWord tau A y p))

def rawDirectedAffineGradientEntry {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) : RawRat :=
  let G := fun i j => rawDirectedNegativeGradientLower tau (A i j)
    (betheAffineMatrixQ y i j) p
  ((G a.castSucc b.castSucc).sub (G a.castSucc (Fin.last m))).sub
      (G (Fin.last m) b.castSucc) |>.add
    (G (Fin.last m) (Fin.last m))

@[simp] theorem machineDirectedAffineGradientEntryDimension_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientEntryDimension
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      List.replicate m true := by
  simp [machineDirectedAffineGradientEntryDimension,
    machineDirectedAffineGradientEntryPayload,
    machineDirectedAffineGradientEntryRest,
    machineDirectedAffineGradientEntryCanonicalWord]

@[simp] theorem machineDirectedAffineGradientUpperLeftInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientUpperLeftInput
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      machineDirectedGradientEntryCanonicalWord tau A y p
        a.castSucc b.castSucc := by
  rfl

@[simp] theorem machineDirectedAffineGradientUpperRightInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientUpperRightInput
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      machineDirectedGradientEntryCanonicalWord tau A y p
        a.castSucc (Fin.last m) := by
  rw [machineDirectedAffineGradientUpperRightInput,
    machineDirectedAffineGradientEntryDimension_encode]
  simp [
    machineDirectedAffineGradientEntryRow,
    machineDirectedAffineGradientEntryRest,
    machineDirectedAffineGradientEntryPayload,
    machineDirectedAffineGradientEntryCanonicalWord,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineDirectedAffineGradientLowerLeftInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientLowerLeftInput
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      machineDirectedGradientEntryCanonicalWord tau A y p
        (Fin.last m) b.castSucc := by
  rw [machineDirectedAffineGradientLowerLeftInput,
    machineDirectedAffineGradientEntryDimension_encode]
  simp [
    machineDirectedAffineGradientEntryColumn,
    machineDirectedAffineGradientEntryRest,
    machineDirectedAffineGradientEntryPayload,
    machineDirectedAffineGradientEntryCanonicalWord,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineDirectedAffineGradientLowerRightInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientLowerRightInput
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      machineDirectedGradientEntryCanonicalWord tau A y p
        (Fin.last m) (Fin.last m) := by
  rw [machineDirectedAffineGradientLowerRightInput,
    machineDirectedAffineGradientEntryDimension_encode]
  simp [
    machineDirectedAffineGradientEntryRest,
    machineDirectedAffineGradientEntryPayload,
    machineDirectedAffineGradientEntryCanonicalWord,
    machineDirectedGradientEntryCanonicalWord]

@[simp] theorem machineDirectedAffineGradientUpperLeftRaw_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientUpperLeftRaw
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rawRatBinaryCode
        (rawDirectedNegativeGradientLower tau (A a.castSucc b.castSucc)
          (betheAffineMatrixQ y a.castSucc b.castSucc) p) := by
  rw [machineDirectedAffineGradientUpperLeftRaw,
    machineDirectedAffineGradientUpperLeftInput_encode,
    machineDirectedNegativeGradientEntryRawCode_encode]

@[simp] theorem machineDirectedAffineGradientUpperRightRaw_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientUpperRightRaw
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rawRatBinaryCode
        (rawDirectedNegativeGradientLower tau (A a.castSucc (Fin.last m))
          (betheAffineMatrixQ y a.castSucc (Fin.last m)) p) := by
  rw [machineDirectedAffineGradientUpperRightRaw,
    machineDirectedAffineGradientUpperRightInput_encode,
    machineDirectedNegativeGradientEntryRawCode_encode]

@[simp] theorem machineDirectedAffineGradientLowerLeftRaw_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientLowerLeftRaw
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rawRatBinaryCode
        (rawDirectedNegativeGradientLower tau (A (Fin.last m) b.castSucc)
          (betheAffineMatrixQ y (Fin.last m) b.castSucc) p) := by
  rw [machineDirectedAffineGradientLowerLeftRaw,
    machineDirectedAffineGradientLowerLeftInput_encode,
    machineDirectedNegativeGradientEntryRawCode_encode]

@[simp] theorem machineDirectedAffineGradientLowerRightRaw_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientLowerRightRaw
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rawRatBinaryCode
        (rawDirectedNegativeGradientLower tau (A (Fin.last m) (Fin.last m))
          (betheAffineMatrixQ y (Fin.last m) (Fin.last m)) p) := by
  rw [machineDirectedAffineGradientLowerRightRaw,
    machineDirectedAffineGradientLowerRightInput_encode,
    machineDirectedNegativeGradientEntryRawCode_encode]

@[simp] theorem machineDirectedAffineGradientEntryRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    machineDirectedAffineGradientEntryRawCode
        (machineDirectedAffineGradientEntryCanonicalWord tau A y p a b) =
      rawRatBinaryCode (rawDirectedAffineGradientEntry tau A y p a b) := by
  simp only [machineDirectedAffineGradientEntryRawCode,
    machineDirectedAffineGradientSecondDifference,
    machineDirectedAffineGradientFirstDifference,
    machineDirectedAffineGradientUpperLeftRaw_encode,
    machineDirectedAffineGradientUpperRightRaw_encode,
    machineDirectedAffineGradientLowerLeftRaw_encode,
    machineDirectedAffineGradientLowerRightRaw_encode]
  rw [
    machineRawRatSubCode_encode, machineRawRatSubCode_encode,
    machineRawRatAddCode_encode]
  rfl

theorem rawDirectedAffineGradientEntry_value {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (a b : Fin m) :
    (rawDirectedAffineGradientEntry tau A y p a b).value =
      affinePullbackGradient
        (directedNegativeGradientLowerMatrix tau A
          (betheAffineMatrixQ y) p) a b := by
  simp [rawDirectedAffineGradientEntry, affinePullbackGradient,
    directedNegativeGradientLowerMatrix,
    RawRat.value_add, RawRat.value_sub,
    rawDirectedNegativeGradientLower_value]

end BeyondBethe
