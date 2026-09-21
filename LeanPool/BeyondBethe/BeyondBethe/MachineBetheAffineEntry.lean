/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheAffineLineSum
import LeanPool.BeyondBethe.BeyondBethe.MachineRowPairDisjoint
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalUnary

/-!
# Exact finite-word entries of the Birkhoff affine recovery

From a flattened `m`-by-`m` rational block, the recovered matrix of order
`m+1` has four kinds of entries: a stored upper-left coordinate, one minus a
row sum, one minus a column sum, and the total sum minus `m-1`.  This file
assembles those four cases as one uniform polynomial-time word machine.
-/

namespace BeyondBethe

open Complexity

def machineBetheAffineEntryDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBetheAffineEntryRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineBetheAffineEntryRow (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheAffineEntryRest word)

def machineBetheAffineEntryColumn (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineBetheAffineEntryRest word))

def machineBetheAffineEntryVector (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machineBetheAffineEntryRest word))

def machineBetheAffineEntryLastRowBit (word : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineBetheAffineEntryRow word)
    (machineBetheAffineEntryDimension word)

def machineBetheAffineEntryLastColumnBit (word : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineBetheAffineEntryColumn word)
    (machineBetheAffineEntryDimension word)

def machineBetheAffineEntryFlatInput (word : List Bool) : List Bool :=
  pair [true]
    (pair (machineBetheAffineEntryDimension word)
      (pair (machineBetheAffineEntryRow word)
        (pair (machineBetheAffineEntryColumn word)
          (machineBetheAffineEntryVector word))))

def machineBetheAffineEntryUpperLeft (word : List Bool) : List Bool :=
  machineBetheFlatEntryRawCode (machineBetheAffineEntryFlatInput word)

def machineBetheAffineEntryRowSumInput (word : List Bool) : List Bool :=
  pair [true]
    (pair (machineBetheAffineEntryDimension word)
      (pair (machineBetheAffineEntryRow word)
        (machineBetheAffineEntryVector word)))

def machineBetheAffineEntryColumnSumInput (word : List Bool) : List Bool :=
  pair [false]
    (pair (machineBetheAffineEntryDimension word)
      (pair (machineBetheAffineEntryColumn word)
        (machineBetheAffineEntryVector word)))

def machineBetheAffineEntryRowSum (word : List Bool) : List Bool :=
  machineBetheLineSumRawCode (machineBetheAffineEntryRowSumInput word)

def machineBetheAffineEntryColumnSum (word : List Bool) : List Bool :=
  machineBetheLineSumRawCode (machineBetheAffineEntryColumnSumInput word)

def machineRawRatSubCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machinePairFirst word)
      (machineRawRatNegCode (machinePairSecond word)))

def machineBetheAffineEntryLastColumn (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineBetheAffineEntryRowSum word))

def machineBetheAffineEntryLastRow (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineBetheAffineEntryColumnSum word))

def machineBetheAffineEntryTotal (word : List Bool) : List Bool :=
  machineRationalVectorRawSumCode (machineBetheAffineEntryVector word)

def machineBetheAffineEntryDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheAffineEntryDimension word)

def machineBetheAffineEntryDimensionMinusOneInteger
    (word : List Bool) : List Bool :=
  machineIntegerAddCode
    (pair (machineNaturalIntegerCode
      (machineBetheAffineEntryDimensionBits word))
      (integerBinaryCode (-1)))

def machineBetheAffineEntryDimensionMinusOneRaw
    (word : List Bool) : List Bool :=
  pair (machineBetheAffineEntryDimensionMinusOneInteger word)
    (1 : ℕ).bits

def machineBetheAffineEntryCorner (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (machineBetheAffineEntryTotal word)
      (machineBetheAffineEntryDimensionMinusOneRaw word))

def machineBetheAffineEntryRawCode (word : List Bool) : List Bool :=
  machineIfHead (machineBetheAffineEntryLastRowBit word)
    (machineIfHead (machineBetheAffineEntryLastColumnBit word)
      (machineBetheAffineEntryCorner word)
      (machineBetheAffineEntryLastRow word))
    (machineIfHead (machineBetheAffineEntryLastColumnBit word)
      (machineBetheAffineEntryLastColumn word)
      (machineBetheAffineEntryUpperLeft word))

theorem machineBetheAffineEntryDimension_mem_FP :
    machineBetheAffineEntryDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheAffineEntryRest_mem_FP :
    machineBetheAffineEntryRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheAffineEntryRow_mem_FP :
    machineBetheAffineEntryRow ∈ FP := by
  simpa only [machineBetheAffineEntryRow] using
    machineCompose_mem_FP machineBetheAffineEntryRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheAffineEntryColumn_mem_FP :
    machineBetheAffineEntryColumn ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheAffineEntryRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheAffineEntryColumn] using
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheAffineEntryVector_mem_FP :
    machineBetheAffineEntryVector ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheAffineEntryRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheAffineEntryVector] using
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineBetheAffineEntryLastRowBit_mem_FP :
    machineBetheAffineEntryLastRowBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    machineBetheAffineEntryRow_mem_FP machineBetheAffineEntryDimension_mem_FP

theorem machineBetheAffineEntryLastColumnBit_mem_FP :
    machineBetheAffineEntryLastColumnBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    machineBetheAffineEntryColumn_mem_FP
    machineBetheAffineEntryDimension_mem_FP

theorem machineBetheAffineEntryFlatInput_mem_FP :
    machineBetheAffineEntryFlatInput ∈ FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [true])
    (machinePair_mem_FP machineBetheAffineEntryDimension_mem_FP
      (machinePair_mem_FP machineBetheAffineEntryRow_mem_FP
        (machinePair_mem_FP machineBetheAffineEntryColumn_mem_FP
          machineBetheAffineEntryVector_mem_FP)))

theorem machineBetheAffineEntryUpperLeft_mem_FP :
    machineBetheAffineEntryUpperLeft ∈ FP := by
  simpa only [machineBetheAffineEntryUpperLeft] using
    machineCompose_mem_FP machineBetheAffineEntryFlatInput_mem_FP
      machineBetheFlatEntryRawCode_mem_FP

theorem machineBetheAffineEntryRowSumInput_mem_FP :
    machineBetheAffineEntryRowSumInput ∈ FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [true])
    (machinePair_mem_FP machineBetheAffineEntryDimension_mem_FP
      (machinePair_mem_FP machineBetheAffineEntryRow_mem_FP
        machineBetheAffineEntryVector_mem_FP))

theorem machineBetheAffineEntryColumnSumInput_mem_FP :
    machineBetheAffineEntryColumnSumInput ∈ FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [false])
    (machinePair_mem_FP machineBetheAffineEntryDimension_mem_FP
      (machinePair_mem_FP machineBetheAffineEntryColumn_mem_FP
        machineBetheAffineEntryVector_mem_FP))

theorem machineBetheAffineEntryRowSum_mem_FP :
    machineBetheAffineEntryRowSum ∈ FP := by
  simpa only [machineBetheAffineEntryRowSum] using
    machineCompose_mem_FP machineBetheAffineEntryRowSumInput_mem_FP
      machineBetheLineSumRawCode_mem_FP

theorem machineBetheAffineEntryColumnSum_mem_FP :
    machineBetheAffineEntryColumnSum ∈ FP := by
  simpa only [machineBetheAffineEntryColumnSum] using
    machineCompose_mem_FP machineBetheAffineEntryColumnSumInput_mem_FP
      machineBetheLineSumRawCode_mem_FP

theorem machineRawRatSubCode_mem_FP : machineRawRatSubCode ∈ FP := by
  have hneg := machineCompose_mem_FP machinePairSecond_mem_FP
    machineRawRatNegCode_mem_FP
  have hinput := machinePair_mem_FP machinePairFirst_mem_FP hneg
  simpa only [machineRawRatSubCode] using
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineBetheAffineEntryLastColumn_mem_FP :
    machineBetheAffineEntryLastColumn ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineBetheAffineEntryRowSum_mem_FP
  simpa only [machineBetheAffineEntryLastColumn] using
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineBetheAffineEntryLastRow_mem_FP :
    machineBetheAffineEntryLastRow ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineBetheAffineEntryColumnSum_mem_FP
  simpa only [machineBetheAffineEntryLastRow] using
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineBetheAffineEntryTotal_mem_FP :
    machineBetheAffineEntryTotal ∈ FP := by
  simpa only [machineBetheAffineEntryTotal] using
    machineCompose_mem_FP machineBetheAffineEntryVector_mem_FP
      machineRationalVectorRawSumCode_mem_FP

theorem machineBetheAffineEntryDimensionBits_mem_FP :
    machineBetheAffineEntryDimensionBits ∈ FP := by
  simpa only [machineBetheAffineEntryDimensionBits] using
    machineCompose_mem_FP machineBetheAffineEntryDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheAffineEntryDimensionMinusOneInteger_mem_FP :
    machineBetheAffineEntryDimensionMinusOneInteger ∈ FP := by
  have hnat := machineCompose_mem_FP
    machineBetheAffineEntryDimensionBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  have hinput := machinePair_mem_FP hnat
    (machineConst_mem_FP (integerBinaryCode (-1)))
  simpa only [machineBetheAffineEntryDimensionMinusOneInteger] using
    machineCompose_mem_FP hinput machineIntegerAddCode_mem_FP

theorem machineBetheAffineEntryDimensionMinusOneRaw_mem_FP :
    machineBetheAffineEntryDimensionMinusOneRaw ∈ FP := by
  exact machinePair_mem_FP
    machineBetheAffineEntryDimensionMinusOneInteger_mem_FP
    (machineConst_mem_FP (1 : ℕ).bits)

theorem machineBetheAffineEntryCorner_mem_FP :
    machineBetheAffineEntryCorner ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheAffineEntryTotal_mem_FP
    machineBetheAffineEntryDimensionMinusOneRaw_mem_FP
  simpa only [machineBetheAffineEntryCorner] using
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineBetheAffineEntryRawCode_mem_FP :
    machineBetheAffineEntryRawCode ∈ FP := by
  have hlastRow := machineIfHead_mem_FP
    machineBetheAffineEntryLastColumnBit_mem_FP
    machineBetheAffineEntryCorner_mem_FP
    machineBetheAffineEntryLastRow_mem_FP
  have hnotLastRow := machineIfHead_mem_FP
    machineBetheAffineEntryLastColumnBit_mem_FP
    machineBetheAffineEntryLastColumn_mem_FP
    machineBetheAffineEntryUpperLeft_mem_FP
  exact machineIfHead_mem_FP machineBetheAffineEntryLastRowBit_mem_FP
    hlastRow hnotLastRow

/-! ## Exact semantics -/

def machineBetheAffineEntryCanonicalWord {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate i.1 true)
      (pair (List.replicate j.1 true) (rationalFiniteVectorCode y)))

def rawBetheDimensionMinusOne (m : ℕ) : RawRat :=
  ⟨(m : ℤ) - 1, 1, by norm_num⟩

def rawBetheAffineEntry {m : ℕ} (y : Fin (m * m) → ℚ)
    (i j : Fin (m + 1)) : RawRat :=
  Fin.lastCases
    (Fin.lastCases
      ((rawRatListSum RawRat.zero (List.ofFn y)).sub
        (rawBetheDimensionMinusOne m))
      (fun j ↦ RawRat.one.sub (rawBetheAffineLineSum false j y)) j)
    (fun i ↦ Fin.lastCases
      (RawRat.one.sub (rawBetheAffineLineSum true i y))
      (fun j ↦ rawRatOfRat (y (finProdFinEquiv (i, j)))) j) i

@[simp] theorem machineUnaryRulersEqualBit_replicate (a b : ℕ) :
    machineUnaryRulersEqualBit (List.replicate a true)
        (List.replicate b true) = [decide (a = b)] := by
  rw [machineUnaryRulersEqualBit]
  simp only [machineLengthBits_encode, List.length_replicate,
    machineBinaryNatEqBit_pair_natBits]

@[simp] theorem rawBetheDimensionMinusOne_value (m : ℕ) :
    (rawBetheDimensionMinusOne m).value = (m : ℚ) - 1 := by
  simp [rawBetheDimensionMinusOne, RawRat.value]

@[simp] theorem machineBetheAffineEntryLastRowBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryLastRowBit
        (machineBetheAffineEntryCanonicalWord i j y) =
      [decide (i = Fin.last m)] := by
  rw [machineBetheAffineEntryLastRowBit]
  simp only [machineBetheAffineEntryRow, machineBetheAffineEntryDimension,
    machineBetheAffineEntryRest, machineBetheAffineEntryCanonicalWord,
    machinePairFirst_pair, machinePairSecond_pair,
    machineUnaryRulersEqualBit_replicate]
  by_cases hi : i = Fin.last m
  · subst i
    simp
  · have hval : i.1 ≠ m := by
      intro h
      apply hi
      apply Fin.ext
      simpa using h
    simp [hi, hval]

@[simp] theorem machineBetheAffineEntryLastColumnBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryLastColumnBit
        (machineBetheAffineEntryCanonicalWord i j y) =
      [decide (j = Fin.last m)] := by
  rw [machineBetheAffineEntryLastColumnBit]
  simp only [machineBetheAffineEntryColumn,
    machineBetheAffineEntryDimension,
    machineBetheAffineEntryRest, machineBetheAffineEntryCanonicalWord,
    machinePairFirst_pair, machinePairSecond_pair,
    machineUnaryRulersEqualBit_replicate]
  by_cases hj : j = Fin.last m
  · subst j
    simp
  · have hval : j.1 ≠ m := by
      intro h
      apply hj
      apply Fin.ext
      simpa using h
    simp [hj, hval]

@[simp] theorem machineRawRatSubCode_encode (q r : RawRat) :
    machineRawRatSubCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rawRatBinaryCode (q.sub r) := by
  rw [machineRawRatSubCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineBetheAffineEntryDimensionMinusOneRaw_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryDimensionMinusOneRaw
        (machineBetheAffineEntryCanonicalWord i j y) =
      rawRatBinaryCode (rawBetheDimensionMinusOne m) := by
  rw [machineBetheAffineEntryDimensionMinusOneRaw,
    machineBetheAffineEntryDimensionMinusOneInteger,
    machineBetheAffineEntryDimensionBits,
    machineBetheAffineEntryDimension,
    machineBetheAffineEntryCanonicalWord]
  simp only [machinePairFirst_pair, machineLengthBits_encode,
    List.length_replicate, machineNaturalIntegerCode_natBits,
    machineIntegerAddCode_encode]
  rfl

@[simp] theorem machineBetheAffineEntryDimension_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryDimension
        (machineBetheAffineEntryCanonicalWord i j y) =
      List.replicate m true := by
  simp [machineBetheAffineEntryDimension,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineBetheAffineEntryRow_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryRow
        (machineBetheAffineEntryCanonicalWord i j y) =
      List.replicate i.1 true := by
  simp [machineBetheAffineEntryRow, machineBetheAffineEntryRest,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineBetheAffineEntryColumn_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryColumn
        (machineBetheAffineEntryCanonicalWord i j y) =
      List.replicate j.1 true := by
  simp [machineBetheAffineEntryColumn, machineBetheAffineEntryRest,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineBetheAffineEntryVector_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryVector
        (machineBetheAffineEntryCanonicalWord i j y) =
      rationalFiniteVectorCode y := by
  simp [machineBetheAffineEntryVector, machineBetheAffineEntryRest,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineBetheAffineEntryFlatInput_encode {m : ℕ}
    (i j : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryFlatInput
        (machineBetheAffineEntryCanonicalWord i.castSucc j.castSucc y) =
      betheFlatIndexCanonicalWord true i j y := by
  simp [machineBetheAffineEntryFlatInput, betheFlatIndexCanonicalWord]

@[simp] theorem machineBetheAffineEntryRowSumInput_encode {m : ℕ}
    (i : Fin m) (j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryRowSumInput
        (machineBetheAffineEntryCanonicalWord i.castSucc j y) =
      machineBetheLineSumCanonicalWord true i y := by
  simp [machineBetheAffineEntryRowSumInput,
    machineBetheLineSumCanonicalWord]

@[simp] theorem machineBetheAffineEntryColumnSumInput_encode {m : ℕ}
    (i : Fin (m + 1)) (j : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryColumnSumInput
        (machineBetheAffineEntryCanonicalWord i j.castSucc y) =
      machineBetheLineSumCanonicalWord false j y := by
  simp [machineBetheAffineEntryColumnSumInput,
    machineBetheLineSumCanonicalWord]

@[simp] theorem machineBetheAffineEntryTotal_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryTotal
        (machineBetheAffineEntryCanonicalWord i j y) =
      rawRatBinaryCode (rawRatListSum RawRat.zero (List.ofFn y)) := by
  rw [machineBetheAffineEntryTotal,
    machineBetheAffineEntryVector_encode]
  simpa only [rationalFiniteVectorCode, rationalVectorBinaryCode] using
    machineRationalVectorRawSumCode_encode y

@[simp] theorem machineBetheAffineEntryCorner_encode {m : ℕ}
    (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryCorner
        (machineBetheAffineEntryCanonicalWord
          (Fin.last m) (Fin.last m) y) =
      rawRatBinaryCode
        ((rawRatListSum RawRat.zero (List.ofFn y)).sub
          (rawBetheDimensionMinusOne m)) := by
  rw [machineBetheAffineEntryCorner]
  rw [machineBetheAffineEntryTotal_encode,
    machineBetheAffineEntryDimensionMinusOneRaw_encode,
    machineRawRatSubCode_encode]

@[simp] theorem machineBetheAffineEntryLastRow_encode {m : ℕ}
    (j : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryLastRow
        (machineBetheAffineEntryCanonicalWord
          (Fin.last m) j.castSucc y) =
      rawRatBinaryCode
        (RawRat.one.sub (rawBetheAffineLineSum false j y)) := by
  rw [machineBetheAffineEntryLastRow]
  rw [machineBetheAffineEntryColumnSum,
    machineBetheAffineEntryColumnSumInput_encode,
    machineBetheLineSumRawCode_encode,
    machineRawRatSubCode_encode]

@[simp] theorem machineBetheAffineEntryLastColumn_encode {m : ℕ}
    (i : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryLastColumn
        (machineBetheAffineEntryCanonicalWord
          i.castSucc (Fin.last m) y) =
      rawRatBinaryCode
        (RawRat.one.sub (rawBetheAffineLineSum true i y)) := by
  rw [machineBetheAffineEntryLastColumn]
  rw [machineBetheAffineEntryRowSum,
    machineBetheAffineEntryRowSumInput_encode,
    machineBetheLineSumRawCode_encode,
    machineRawRatSubCode_encode]

@[simp] theorem machineBetheAffineEntryUpperLeft_encode {m : ℕ}
    (i j : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryUpperLeft
        (machineBetheAffineEntryCanonicalWord i.castSucc j.castSucc y) =
      rawRatBinaryCode (rawRatOfRat (y (finProdFinEquiv (i, j)))) := by
  rw [machineBetheAffineEntryUpperLeft]
  rw [machineBetheAffineEntryFlatInput_encode,
    machineBetheFlatEntryRawCode_encode]
  simp

@[simp] theorem machineBetheAffineEntryRawCode_encode {m : ℕ}
    (i j : Fin (m + 1)) (y : Fin (m * m) → ℚ) :
    machineBetheAffineEntryRawCode
        (machineBetheAffineEntryCanonicalWord i j y) =
      rawRatBinaryCode (rawBetheAffineEntry y i j) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [machineBetheAffineEntryRawCode, rawBetheAffineEntry]
  · have hj : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
    simp [machineBetheAffineEntryRawCode, rawBetheAffineEntry, hj]
  · have hi : i.castSucc ≠ Fin.last m := Fin.castSucc_ne_last i
    simp [machineBetheAffineEntryRawCode, rawBetheAffineEntry, hi]
  · have hi : i.castSucc ≠ Fin.last m := Fin.castSucc_ne_last i
    have hj : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
    simp [machineBetheAffineEntryRawCode, rawBetheAffineEntry, hi, hj]

theorem rawBetheAffineEntry_value {m : ℕ} (y : Fin (m * m) → ℚ)
    (i j : Fin (m + 1)) :
    (rawBetheAffineEntry y i j).value = betheAffineMatrixQ y i j := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [rawBetheAffineEntry, Fin.lastCases_last]
    rw [betheAffineMatrixQ,
      birkhoffAffineMap_last_last, RawRat.value_sub,
      rawBetheDimensionMinusOne_value]
    have hsum := sum_squareMatrixToVector (vectorToSquareMatrix y)
    simp only [squareMatrixToVector_vectorToSquareMatrix] at hsum
    rw [rawRatListSum_ofFn_value, hsum]
  · simp only [rawBetheAffineEntry, Fin.lastCases_last,
      Fin.lastCases_castSucc]
    rw [betheAffineMatrixQ,
      birkhoffAffineMap_last_castSucc, RawRat.value_sub,
      RawRat.value_one, rawBetheAffineLineSum_value]
    simp [vectorToSquareMatrix]
  · simp only [rawBetheAffineEntry, Fin.lastCases_last,
      Fin.lastCases_castSucc]
    rw [betheAffineMatrixQ,
      birkhoffAffineMap_castSucc_last, RawRat.value_sub,
      RawRat.value_one, rawBetheAffineLineSum_value]
    simp [vectorToSquareMatrix]
  · simp [rawBetheAffineEntry, Fin.lastCases_castSucc,
      betheAffineMatrixQ,
      vectorToSquareMatrix, rawRatOfRat_value]

end BeyondBethe
