/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalBallInit
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidCenterUpdate

/-!
# Polynomial-time rows of the ellipsoid direction update

For a unary row index `i`, dimension, and cut-direction vector `b`, this
module constructs the `i`th row of the rank-one matrix

`A I - ((A-p) / ||b||^2) b b^T`.

The diagonal row is built by updating an encoded zero vector, while the
rank-one row is produced by one scalar-vector multiplication.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def rationalDirectionDiagonalRow {d : ℕ}
    (A : ℚ) (i : Fin d) : Fin d → ℚ :=
  fun j ↦ if i = j then A else 0

def rawDirectionNormSq {d : ℕ} (b : Fin d → ℚ) : RawRat :=
  rawRatListDot RawRat.zero (List.ofFn b) (List.ofFn b)

def rawDirectionGap (d : ℕ) : RawRat :=
  (rawEllipsoidPerpScale d).sub (rawEllipsoidParallelScale d)

def rawDirectionCoefficient {d : ℕ} (b : Fin d → ℚ) : RawRat :=
  (rawDirectionGap d).div (rawDirectionNormSq b)

def rawDirectionRowScale {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) : RawRat :=
  (rawDirectionCoefficient b).mul (rawRatOfRat (b i))

def machineDirectionRowIndex (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDirectionRowPayload (word : List Bool) : List Bool :=
  machinePairSecond word

def machineDirectionRowDimensionUnary
    (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectionRowPayload word)

def machineDirectionRowDimensionAndVector
    (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectionRowPayload word)

def machineDirectionRowDimensionBits
    (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectionRowDimensionAndVector word)

def machineDirectionRowVectorCode
    (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectionRowDimensionAndVector word)

def machineDirectionRowNormSqRawCode
    (word : List Bool) : List Bool :=
  machineRationalVectorDotRawCode
    (pair (machineDirectionRowVectorCode word)
      (machineDirectionRowVectorCode word))

def machineDirectionRowGapRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair
      (machineEllipsoidPerpScaleRawCode
        (machineDirectionRowDimensionBits word))
      (machineRawRatNegCode
        (machineEllipsoidParallelScaleRawCode
          (machineDirectionRowDimensionBits word))))

def machineDirectionRowCoefficientRawCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineDirectionRowGapRawCode word)
      (machineDirectionRowNormSqRawCode word))

def machineDirectionRowBEntry
    (word : List Bool) : List Bool :=
  machineListIndex
    (pair (machineDirectionRowIndex word)
      (machineDirectionRowVectorCode word))

def machineDirectionRowScaleRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectionRowCoefficientRawCode word)
      (machineDirectionRowBEntry word))

def machineDirectionRowScaledVectorCode
    (word : List Bool) : List Bool :=
  machineRationalVectorScaleCode
    (pair (machineDirectionRowScaleRawCode word)
      (machineDirectionRowVectorCode word))

def machineDirectionRowZeroVectorCode
    (word : List Bool) : List Bool :=
  machineRationalZeroVectorCode
    (machineDirectionRowDimensionUnary word)

def machineDirectionRowDiagonalCode
    (word : List Bool) : List Bool :=
  machineListUpdate
    (pair (machineDirectionRowIndex word)
      (pair
        (machineEllipsoidPerpScaleEntryCode
          (machineDirectionRowDimensionBits word))
        (machineDirectionRowZeroVectorCode word)))

def machineRationalDirectionUpdateRowCode
    (word : List Bool) : List Bool :=
  machineRationalVectorSubCode
    (pair (machineDirectionRowDimensionUnary word)
      (pair (machineDirectionRowDiagonalCode word)
        (machineDirectionRowScaledVectorCode word)))

/-! ## Polynomial-time closure -/

theorem machineDirectionRowIndex_mem_FP :
    machineDirectionRowIndex ∈ FP := machinePairFirst_mem_FP

theorem machineDirectionRowPayload_mem_FP :
    machineDirectionRowPayload ∈ FP := machinePairSecond_mem_FP

theorem machineDirectionRowDimensionUnary_mem_FP :
    machineDirectionRowDimensionUnary ∈ FP := by
  simpa only [machineDirectionRowDimensionUnary] using!
    machineCompose_mem_FP machineDirectionRowPayload_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectionRowDimensionAndVector_mem_FP :
    machineDirectionRowDimensionAndVector ∈ FP := by
  simpa only [machineDirectionRowDimensionAndVector] using!
    machineCompose_mem_FP machineDirectionRowPayload_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectionRowDimensionBits_mem_FP :
    machineDirectionRowDimensionBits ∈ FP := by
  simpa only [machineDirectionRowDimensionBits] using!
    machineCompose_mem_FP machineDirectionRowDimensionAndVector_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectionRowVectorCode_mem_FP :
    machineDirectionRowVectorCode ∈ FP := by
  simpa only [machineDirectionRowVectorCode] using!
    machineCompose_mem_FP machineDirectionRowDimensionAndVector_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectionRowNormSqRawCode_mem_FP :
    machineDirectionRowNormSqRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineDirectionRowVectorCode_mem_FP
    machineDirectionRowVectorCode_mem_FP
  simpa only [machineDirectionRowNormSqRawCode] using!
    machineCompose_mem_FP hinput machineRationalVectorDotRawCode_mem_FP

theorem machineDirectionRowGapRawCode_mem_FP :
    machineDirectionRowGapRawCode ∈ FP := by
  have hperp := machineCompose_mem_FP machineDirectionRowDimensionBits_mem_FP
    machineEllipsoidPerpScaleRawCode_mem_FP
  have hparallel := machineCompose_mem_FP
    machineDirectionRowDimensionBits_mem_FP
    machineEllipsoidParallelScaleRawCode_mem_FP
  have hneg := machineCompose_mem_FP hparallel machineRawRatNegCode_mem_FP
  simpa only [machineDirectionRowGapRawCode] using!
    machineCompose_mem_FP (machinePair_mem_FP hperp hneg)
      machineRawRatAddCode_mem_FP

theorem machineDirectionRowCoefficientRawCode_mem_FP :
    machineDirectionRowCoefficientRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineDirectionRowGapRawCode_mem_FP
    machineDirectionRowNormSqRawCode_mem_FP
  simpa only [machineDirectionRowCoefficientRawCode] using!
    machineCompose_mem_FP hinput machineRawRatDivCode_mem_FP

theorem machineDirectionRowBEntry_mem_FP :
    machineDirectionRowBEntry ∈ FP := by
  have hinput := machinePair_mem_FP machineDirectionRowIndex_mem_FP
    machineDirectionRowVectorCode_mem_FP
  simpa only [machineDirectionRowBEntry] using!
    machineCompose_mem_FP hinput machineListIndex_mem_FP

theorem machineDirectionRowScaleRawCode_mem_FP :
    machineDirectionRowScaleRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectionRowCoefficientRawCode_mem_FP
    machineDirectionRowBEntry_mem_FP
  simpa only [machineDirectionRowScaleRawCode] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectionRowScaledVectorCode_mem_FP :
    machineDirectionRowScaledVectorCode ∈ FP := by
  have hinput := machinePair_mem_FP machineDirectionRowScaleRawCode_mem_FP
    machineDirectionRowVectorCode_mem_FP
  simpa only [machineDirectionRowScaledVectorCode] using!
    machineCompose_mem_FP hinput machineRationalVectorScaleCode_mem_FP

theorem machineDirectionRowZeroVectorCode_mem_FP :
    machineDirectionRowZeroVectorCode ∈ FP := by
  simpa only [machineDirectionRowZeroVectorCode] using!
    machineCompose_mem_FP machineDirectionRowDimensionUnary_mem_FP
      machineRationalZeroVectorCode_mem_FP

theorem machineDirectionRowDiagonalCode_mem_FP :
    machineDirectionRowDiagonalCode ∈ FP := by
  have hperp := machineCompose_mem_FP machineDirectionRowDimensionBits_mem_FP
    machineEllipsoidPerpScaleEntryCode_mem_FP
  have hpayload := machinePair_mem_FP hperp
    machineDirectionRowZeroVectorCode_mem_FP
  have hinput := machinePair_mem_FP machineDirectionRowIndex_mem_FP hpayload
  simpa only [machineDirectionRowDiagonalCode] using!
    machineCompose_mem_FP hinput machineListUpdate_mem_FP

theorem machineRationalDirectionUpdateRowCode_mem_FP :
    machineRationalDirectionUpdateRowCode ∈ FP := by
  have hpayload := machinePair_mem_FP machineDirectionRowDiagonalCode_mem_FP
    machineDirectionRowScaledVectorCode_mem_FP
  have hinput := machinePair_mem_FP machineDirectionRowDimensionUnary_mem_FP
    hpayload
  simpa only [machineRationalDirectionUpdateRowCode] using!
    machineCompose_mem_FP hinput machineRationalVectorSubCode_mem_FP

/-! ## Exact semantics -/

@[simp] theorem rawDirectionNormSq_value {d : ℕ} (b : Fin d → ℚ) :
    (rawDirectionNormSq b).value = finiteNormSq b := by
  rw [rawDirectionNormSq, rawRatListDot_ofFn_value]
  rfl

@[simp] theorem rawDirectionGap_value (d : ℕ) :
    (rawDirectionGap d).value =
      rationalEllipsoidPerpScale d - rationalEllipsoidParallelScale d := by
  simp [rawDirectionGap, RawRat.sub, RawRat.value_add,
    RawRat.value_neg, sub_eq_add_neg]

@[simp] theorem rawDirectionCoefficient_value {d : ℕ}
    (b : Fin d → ℚ) :
    (rawDirectionCoefficient b).value =
      (rationalEllipsoidPerpScale d -
        rationalEllipsoidParallelScale d) / finiteNormSq b := by
  simp [rawDirectionCoefficient]

@[simp] theorem rawDirectionRowScale_value {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    (rawDirectionRowScale b i).value =
      ((rationalEllipsoidPerpScale d -
        rationalEllipsoidParallelScale d) / finiteNormSq b) * b i := by
  simp [rawDirectionRowScale]

@[simp] theorem machineDirectionRowNormSqRawCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowNormSqRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true) (pair d.bits
            (rationalFiniteVectorCode b)))) =
      rawRatBinaryCode (rawDirectionNormSq b) := by
  rw [machineDirectionRowNormSqRawCode]
  simp only [machineDirectionRowVectorCode,
    machineDirectionRowDimensionAndVector, machineDirectionRowPayload,
    machinePairSecond_pair, machineRationalVectorDotRawCode_encode,
    rawDirectionNormSq]

@[simp] theorem machineDirectionRowGapRawCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowGapRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rawRatBinaryCode (rawDirectionGap d) := by
  rw [machineDirectionRowGapRawCode]
  simp only [machineDirectionRowDimensionBits,
    machineDirectionRowDimensionAndVector, machineDirectionRowPayload,
    machinePairSecond_pair, machinePairFirst_pair,
    machineEllipsoidPerpScaleRawCode_encode,
    machineEllipsoidParallelScaleRawCode_encode,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode,
    rawDirectionGap, RawRat.sub]

@[simp] theorem machineDirectionRowCoefficientRawCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowCoefficientRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rawRatBinaryCode (rawDirectionCoefficient b) := by
  rw [machineDirectionRowCoefficientRawCode]
  simp only [machineDirectionRowGapRawCode_encode,
    machineDirectionRowNormSqRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineDirectionRowBEntry_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowBEntry
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rationalEntryBinaryCode (b i) := by
  rw [machineDirectionRowBEntry]
  simp only [machineDirectionRowIndex, machinePairFirst_pair,
    machineDirectionRowVectorCode, machineDirectionRowDimensionAndVector,
    machineDirectionRowPayload, machinePairSecond_pair,
    rationalFiniteVectorCode]
  rw [machineListIndex_binaryListCode]
  · simp
  · simp

@[simp] theorem machineDirectionRowScaleRawCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowScaleRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rawRatBinaryCode (rawDirectionRowScale b i) := by
  rw [machineDirectionRowScaleRawCode]
  simp only [machineDirectionRowCoefficientRawCode_encode,
    machineDirectionRowBEntry_encode,
    ← rawRatBinaryCode_rawRatOfRat, machineRawRatMulCode_encode,
    rawDirectionRowScale]

@[simp] theorem machineDirectionRowScaledVectorCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowScaledVectorCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rationalFiniteVectorCode
        (rationalVectorScale (rawDirectionRowScale b i).value b) := by
  rw [machineDirectionRowScaledVectorCode]
  simp only [machineDirectionRowScaleRawCode_encode,
    machineDirectionRowVectorCode, machineDirectionRowDimensionAndVector,
    machineDirectionRowPayload, machinePairSecond_pair]
  rw [machineRationalVectorScaleCode_encode]

@[simp] theorem machineDirectionRowDiagonalCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineDirectionRowDiagonalCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rationalFiniteVectorCode
        (rationalDirectionDiagonalRow (rationalEllipsoidPerpScale d) i) := by
  rw [machineDirectionRowDiagonalCode]
  simp only [machineDirectionRowIndex, machinePairFirst_pair,
    machineDirectionRowDimensionBits,
    machineDirectionRowDimensionAndVector, machineDirectionRowPayload,
    machinePairSecond_pair, machineEllipsoidPerpScaleEntryCode_encode,
    machineDirectionRowZeroVectorCode,
    machineDirectionRowDimensionUnary, machinePairFirst_pair,
    machineRationalZeroVectorCode_encode]
  change machineListUpdate
      (machineListUpdateCanonicalInput rationalEntryBinaryCode
        (List.ofFn (fun _ : Fin d ↦ (0 : ℚ)))
        (rationalEllipsoidPerpScale d) i.1) = _
  rw [machineListUpdate_binaryListCode]
  · rw [rationalFiniteVectorCode]
    congr 1
    apply List.ext_getElem
    · simp
    · intro j hjLeft hjRight
      by_cases hji : j = i.1
      · subst j
        simp [rationalDirectionDiagonalRow]
      · have hfin : i ≠ ⟨j, by simpa using! hjRight⟩ := by
          intro h
          apply hji
          exact (congrArg Fin.val h).symm
        have hij : i.1 ≠ j := Ne.symm hji
        simp [List.getElem_set, hij, rationalDirectionDiagonalRow, hfin]
  · simpa using! i.isLt

theorem rationalDirectionUpdateRow_eq {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    rationalVectorSub
        (rationalDirectionDiagonalRow (rationalEllipsoidPerpScale d) i)
        (rationalVectorScale (rawDirectionRowScale b i).value b) =
      fun j ↦ directionUpdateMatrix
        (rationalEllipsoidPerpScale d)
        (rationalEllipsoidParallelScale d) b i j := by
  funext j
  simp [rationalVectorSub, rationalDirectionDiagonalRow,
    rationalVectorScale, directionUpdateMatrix]

@[simp] theorem machineRationalDirectionUpdateRowCode_encode {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    machineRationalDirectionUpdateRowCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate d true)
            (pair d.bits (rationalFiniteVectorCode b)))) =
      rationalFiniteVectorCode
        (fun j ↦ directionUpdateMatrix
          (rationalEllipsoidPerpScale d)
          (rationalEllipsoidParallelScale d) b i j) := by
  rw [machineRationalDirectionUpdateRowCode]
  simp only [machineDirectionRowDimensionUnary,
    machineDirectionRowPayload, machinePairSecond_pair,
    machinePairFirst_pair, machineDirectionRowDiagonalCode_encode,
    machineDirectionRowScaledVectorCode_encode]
  change machineRationalVectorSubCode
      (rationalVectorSubCanonicalWord
        (rationalDirectionDiagonalRow (rationalEllipsoidPerpScale d) i)
        (rationalVectorScale (rawDirectionRowScale b i).value b)) = _
  rw [machineRationalVectorSubCode_encode,
    rationalDirectionUpdateRow_eq]

end BeyondBethe
