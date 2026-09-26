/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraph
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorSum
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalTransposeMulVector

/-!
# Finite-word row and column sums for Birkhoff affine coordinates

The Bethe epigraph stores only the upper-left `m`-by-`m` affine block as a
flat rational vector.  This file supplies the first reusable machine needed
by the separation oracle: exact row and column sums of that block.  A Boolean
tag selects a row (`true`) or a column (`false`).  Every index manipulated by
the machine is unary and is obtained from verified binary multiplication and
addition under the complete input word as a guard.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## A verified flattened-coordinate lookup -/

/-- Extract the row-versus-column mode word from a flattened-index request. -/
def machineBetheFlatIndexMode (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the payload following the flattened-index mode word. -/
def machineBetheFlatIndexRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the unary dimension ruler from a flattened-index request. -/
def machineBetheFlatIndexDimension (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFlatIndexRest word)

/-- Extract the unary fixed row or column index from a flattened-index request. -/
def machineBetheFlatIndexFixed (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineBetheFlatIndexRest word))

/-- Extract the unary varying index from a flattened-index request. -/
def machineBetheFlatIndexCurrent (word : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machineBetheFlatIndexRest word)))

/-- Extract the encoded rational vector carried by a flattened-index request. -/
def machineBetheFlatIndexVector (word : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machineBetheFlatIndexRest word)))

/-- Convert the flattened-index dimension ruler to binary. -/
def machineBetheFlatIndexDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheFlatIndexDimension word)

/-- Convert the fixed-index ruler to binary. -/
def machineBetheFlatIndexFixedBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheFlatIndexFixed word)

/-- Convert the varying-index ruler to binary. -/
def machineBetheFlatIndexCurrentBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheFlatIndexCurrent word)

/-- Compute the binary row-mode offset `fixed * dimension + current`. -/
def machineBetheFlatIndexRowBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair
      (machineBinaryMulBits
        (pair (machineBetheFlatIndexFixedBits word)
          (machineBetheFlatIndexDimensionBits word)))
      (machineBetheFlatIndexCurrentBits word))

/-- Compute the binary column-mode offset `current * dimension + fixed`. -/
def machineBetheFlatIndexColumnBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair
      (machineBinaryMulBits
        (pair (machineBetheFlatIndexCurrentBits word)
          (machineBetheFlatIndexDimensionBits word)))
      (machineBetheFlatIndexFixedBits word))

/-- Select the binary flattened offset according to the row-versus-column mode. -/
def machineBetheFlatIndexBits (word : List Bool) : List Bool :=
  machineIfHead (machineBetheFlatIndexMode word)
    (machineBetheFlatIndexRowBits word)
    (machineBetheFlatIndexColumnBits word)

/-- Convert the flattened binary index to a unary ruler bounded by the input word. -/
def machineBetheFlatIndexRuler (word : List Bool) : List Bool :=
  machineBoundedUnary (pair word (machineBetheFlatIndexBits word))

/-- Return the selected canonical rational entry.  Canonical rational-entry
codes and `RawRat` codes coincide, so the result may be fed directly to the
unreduced rational arithmetic machines. -/
def machineBetheFlatEntryRawCode (word : List Bool) : List Bool :=
  machineListIndex
    (pair (machineBetheFlatIndexRuler word)
      (machineBetheFlatIndexVector word))

theorem machineBetheFlatIndexMode_mem_FP :
    machineBetheFlatIndexMode ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFlatIndexRest_mem_FP :
    machineBetheFlatIndexRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFlatIndexDimension_mem_FP :
    machineBetheFlatIndexDimension ∈ FP := by
  simpa only [machineBetheFlatIndexDimension] using!
    machineCompose_mem_FP machineBetheFlatIndexRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFlatIndexFixed_mem_FP :
    machineBetheFlatIndexFixed ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheFlatIndexRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheFlatIndexFixed] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheFlatIndexCurrent_mem_FP :
    machineBetheFlatIndexCurrent ∈ FP := by
  have htail₁ := machineCompose_mem_FP machineBetheFlatIndexRest_mem_FP
    machinePairSecond_mem_FP
  have htail₂ := machineCompose_mem_FP htail₁ machinePairSecond_mem_FP
  simpa only [machineBetheFlatIndexCurrent] using!
    machineCompose_mem_FP htail₂ machinePairFirst_mem_FP

theorem machineBetheFlatIndexVector_mem_FP :
    machineBetheFlatIndexVector ∈ FP := by
  have htail₁ := machineCompose_mem_FP machineBetheFlatIndexRest_mem_FP
    machinePairSecond_mem_FP
  have htail₂ := machineCompose_mem_FP htail₁ machinePairSecond_mem_FP
  simpa only [machineBetheFlatIndexVector] using!
    machineCompose_mem_FP htail₂ machinePairSecond_mem_FP

theorem machineBetheFlatIndexDimensionBits_mem_FP :
    machineBetheFlatIndexDimensionBits ∈ FP := by
  simpa only [machineBetheFlatIndexDimensionBits] using!
    machineCompose_mem_FP machineBetheFlatIndexDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheFlatIndexFixedBits_mem_FP :
    machineBetheFlatIndexFixedBits ∈ FP := by
  simpa only [machineBetheFlatIndexFixedBits] using!
    machineCompose_mem_FP machineBetheFlatIndexFixed_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheFlatIndexCurrentBits_mem_FP :
    machineBetheFlatIndexCurrentBits ∈ FP := by
  simpa only [machineBetheFlatIndexCurrentBits] using!
    machineCompose_mem_FP machineBetheFlatIndexCurrent_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheFlatIndexRowBits_mem_FP :
    machineBetheFlatIndexRowBits ∈ FP := by
  have hmulInput := machinePair_mem_FP
    machineBetheFlatIndexFixedBits_mem_FP
    machineBetheFlatIndexDimensionBits_mem_FP
  have hmul := machineCompose_mem_FP hmulInput
    machineBinaryMulBits_mem_FP
  have haddInput := machinePair_mem_FP hmul
    machineBetheFlatIndexCurrentBits_mem_FP
  simpa only [machineBetheFlatIndexRowBits] using!
    machineCompose_mem_FP haddInput machineBinaryAddBits_mem_FP

theorem machineBetheFlatIndexColumnBits_mem_FP :
    machineBetheFlatIndexColumnBits ∈ FP := by
  have hmulInput := machinePair_mem_FP
    machineBetheFlatIndexCurrentBits_mem_FP
    machineBetheFlatIndexDimensionBits_mem_FP
  have hmul := machineCompose_mem_FP hmulInput
    machineBinaryMulBits_mem_FP
  have haddInput := machinePair_mem_FP hmul
    machineBetheFlatIndexFixedBits_mem_FP
  simpa only [machineBetheFlatIndexColumnBits] using!
    machineCompose_mem_FP haddInput machineBinaryAddBits_mem_FP

theorem machineBetheFlatIndexBits_mem_FP :
    machineBetheFlatIndexBits ∈ FP := by
  exact machineIfHead_mem_FP machineBetheFlatIndexMode_mem_FP
    machineBetheFlatIndexRowBits_mem_FP
    machineBetheFlatIndexColumnBits_mem_FP

theorem machineBetheFlatIndexRuler_mem_FP :
    machineBetheFlatIndexRuler ∈ FP := by
  have hinput := machinePair_mem_FP id_mem_FP
    machineBetheFlatIndexBits_mem_FP
  simpa only [machineBetheFlatIndexRuler] using!
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineBetheFlatEntryRawCode_mem_FP :
    machineBetheFlatEntryRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheFlatIndexRuler_mem_FP
    machineBetheFlatIndexVector_mem_FP
  simpa only [machineBetheFlatEntryRawCode] using!
    machineCompose_mem_FP hinput machineListIndex_mem_FP

/-- The canonical flattened-index request with mode, unary indices, and rational-vector payload. -/
def betheFlatIndexCanonicalWord {m : ℕ} (rowMode : Bool)
    (fixed current : Fin m) (y : Fin (m * m) → ℚ) : List Bool :=
  pair [rowMode]
    (pair (List.replicate m true)
      (pair (List.replicate fixed.1 true)
        (pair (List.replicate current.1 true)
          (rationalFiniteVectorCode y))))

@[simp] theorem machineBetheFlatIndexRowBits_encode {m : ℕ}
    (fixed current : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheFlatIndexRowBits
        (betheFlatIndexCanonicalWord true fixed current y) =
      (fixed.1 * m + current.1).bits := by
  simp [machineBetheFlatIndexRowBits, machineBetheFlatIndexFixedBits,
    machineBetheFlatIndexCurrentBits, machineBetheFlatIndexDimensionBits,
    machineBetheFlatIndexFixed, machineBetheFlatIndexCurrent,
    machineBetheFlatIndexDimension, machineBetheFlatIndexRest,
    betheFlatIndexCanonicalWord, machineBinaryMulBits_pair_natBits,
    machineBinaryAddBits_pair_natBits]

@[simp] theorem machineBetheFlatIndexColumnBits_encode {m : ℕ}
    (fixed current : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheFlatIndexColumnBits
        (betheFlatIndexCanonicalWord false fixed current y) =
      (current.1 * m + fixed.1).bits := by
  simp [machineBetheFlatIndexColumnBits, machineBetheFlatIndexFixedBits,
    machineBetheFlatIndexCurrentBits, machineBetheFlatIndexDimensionBits,
    machineBetheFlatIndexFixed, machineBetheFlatIndexCurrent,
    machineBetheFlatIndexDimension, machineBetheFlatIndexRest,
    betheFlatIndexCanonicalWord, machineBinaryMulBits_pair_natBits,
    machineBinaryAddBits_pair_natBits]

theorem bethe_flat_index_lt_word_length {m : ℕ} (rowMode : Bool)
    (fixed current : Fin m) (y : Fin (m * m) → ℚ) :
    (if rowMode then fixed.1 * m + current.1
      else current.1 * m + fixed.1) ≤
      (betheFlatIndexCanonicalWord rowMode fixed current y).length := by
  have hidx : (if rowMode then fixed.1 * m + current.1
      else current.1 * m + fixed.1) < m * m := by
    cases rowMode with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        calc
          current.1 * m + fixed.1 < current.1 * m + m :=
            Nat.add_lt_add_left fixed.isLt _
          _ = (current.1 + 1) * m := (Nat.succ_mul current.1 m).symm
          _ ≤ m * m := Nat.mul_le_mul_right m
            (Nat.succ_le_iff.mpr current.isLt)
    | true =>
        simp only [if_true]
        calc
          fixed.1 * m + current.1 < fixed.1 * m + m :=
            Nat.add_lt_add_left current.isLt _
          _ = (fixed.1 + 1) * m := (Nat.succ_mul fixed.1 m).symm
          _ ≤ m * m := Nat.mul_le_mul_right m
            (Nat.succ_le_iff.mpr fixed.isLt)
  have hvector : m * m ≤ (rationalFiniteVectorCode y).length := by
    simpa only [rationalFiniteVectorCode, List.length_ofFn] using!
      list_length_le_binaryListCode_length rationalEntryBinaryCode
        (List.ofFn y)
  have hcode : (rationalFiniteVectorCode y).length ≤
      (betheFlatIndexCanonicalWord rowMode fixed current y).length := by
    simp [betheFlatIndexCanonicalWord]
    omega
  exact hidx.le.trans (hvector.trans hcode)

@[simp] theorem machineBetheFlatIndexRuler_encode {m : ℕ}
    (rowMode : Bool) (fixed current : Fin m)
    (y : Fin (m * m) → ℚ) :
    machineBetheFlatIndexRuler
        (betheFlatIndexCanonicalWord rowMode fixed current y) =
      List.replicate
        (if rowMode then fixed.1 * m + current.1
          else current.1 * m + fixed.1) true := by
  rw [machineBetheFlatIndexRuler]
  cases rowMode with
  | false =>
      simp only [machineBetheFlatIndexBits, machineBetheFlatIndexMode,
        betheFlatIndexCanonicalWord, machinePairFirst_pair,
        machineIfHead_false, Bool.false_eq_true, ite_false]
      change machineBoundedUnary
        (pair (betheFlatIndexCanonicalWord false fixed current y)
          (machineBetheFlatIndexColumnBits
            (betheFlatIndexCanonicalWord false fixed current y))) = _
      rw [machineBetheFlatIndexColumnBits_encode]
      rw [machineBoundedUnary_encode_of_le]
      exact bethe_flat_index_lt_word_length false fixed current y
  | true =>
      simp only [machineBetheFlatIndexBits, machineBetheFlatIndexMode,
        betheFlatIndexCanonicalWord, machinePairFirst_pair,
        machineIfHead_true, if_true]
      change machineBoundedUnary
        (pair (betheFlatIndexCanonicalWord true fixed current y)
          (machineBetheFlatIndexRowBits
            (betheFlatIndexCanonicalWord true fixed current y))) = _
      rw [machineBetheFlatIndexRowBits_encode]
      rw [machineBoundedUnary_encode_of_le]
      exact bethe_flat_index_lt_word_length true fixed current y

@[simp] theorem machineBetheFlatIndexVector_encode {m : ℕ}
    (rowMode : Bool) (fixed current : Fin m)
    (y : Fin (m * m) → ℚ) :
    machineBetheFlatIndexVector
        (betheFlatIndexCanonicalWord rowMode fixed current y) =
      rationalFiniteVectorCode y := by
  simp [machineBetheFlatIndexVector, machineBetheFlatIndexRest,
    betheFlatIndexCanonicalWord]

@[simp] theorem machineBetheFlatEntryRawCode_encode {m : ℕ}
    (rowMode : Bool) (fixed current : Fin m)
    (y : Fin (m * m) → ℚ) :
    machineBetheFlatEntryRawCode
        (betheFlatIndexCanonicalWord rowMode fixed current y) =
      rawRatBinaryCode
        (rawRatOfRat
          (if rowMode then y (finProdFinEquiv (fixed, current))
            else y (finProdFinEquiv (current, fixed)))) := by
  rw [machineBetheFlatEntryRawCode,
    machineBetheFlatIndexRuler_encode,
    machineBetheFlatIndexVector_encode]
  cases rowMode with
  | false =>
      simp only [Bool.false_eq_true, ite_false, rationalFiniteVectorCode]
      have hk : current.1 * m + fixed.1 < (List.ofFn y).length := by
        simp only [List.length_ofFn]
        calc
          current.1 * m + fixed.1 < current.1 * m + m :=
            Nat.add_lt_add_left fixed.isLt _
          _ = (current.1 + 1) * m := (Nat.succ_mul current.1 m).symm
          _ ≤ m * m := Nat.mul_le_mul_right m
            (Nat.succ_le_iff.mpr current.isLt)
      rw [machineListIndex_binaryListCode rationalEntryBinaryCode
        (List.ofFn y) (current.1 * m + fixed.1) hk,
        rawRatBinaryCode_rawRatOfRat]
      apply congrArg rationalEntryBinaryCode
      rw [List.getElem_ofFn]
      apply congrArg y
      apply Fin.ext
      simp only [finProdFinEquiv, Equiv.coe_fn_mk]
      rw [Nat.mul_comm current.1 m]
      omega
  | true =>
      simp only [if_true, rationalFiniteVectorCode]
      have hk : fixed.1 * m + current.1 < (List.ofFn y).length := by
        simp only [List.length_ofFn]
        calc
          fixed.1 * m + current.1 < fixed.1 * m + m :=
            Nat.add_lt_add_left current.isLt _
          _ = (fixed.1 + 1) * m := (Nat.succ_mul fixed.1 m).symm
          _ ≤ m * m := Nat.mul_le_mul_right m
            (Nat.succ_le_iff.mpr fixed.isLt)
      rw [machineListIndex_binaryListCode rationalEntryBinaryCode
        (List.ofFn y) (fixed.1 * m + current.1) hk,
        rawRatBinaryCode_rawRatOfRat]
      apply congrArg rationalEntryBinaryCode
      rw [List.getElem_ofFn]
      apply congrArg y
      apply Fin.ext
      simp only [finProdFinEquiv, Equiv.coe_fn_mk]
      rw [Nat.mul_comm fixed.1 m]
      omega

/-! ## A bounded exact line-sum iteration -/

/-- Extract the row-versus-column mode from a line-sum request. -/
def machineBetheLineSumMode (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the payload following the line-sum mode word. -/
def machineBetheLineSumRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the unary dimension ruler from a line-sum request. -/
def machineBetheLineSumDimension (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheLineSumRest word)

/-- Extract the unary fixed row or column index from a line-sum request. -/
def machineBetheLineSumFixed (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineBetheLineSumRest word))

/-- Extract the encoded rational vector from a line-sum request. -/
def machineBetheLineSumVector (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machineBetheLineSumRest word))

/-- Encode the remaining count, current index, accumulator, payload, and bound of a line-sum
state. -/
def machineBetheLineSumPack (remaining current acc payload bound : List Bool) :
    List Bool :=
  pair remaining (pair current (pair acc (pair payload bound)))

/-- Extract the remaining-iteration ruler from a line-sum state. -/
def machineBetheLineSumRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extract the current-index ruler from a line-sum state. -/
def machineBetheLineSumCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extract the encoded raw-rational accumulator from a line-sum state. -/
def machineBetheLineSumAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extract the original line-sum request retained in the state. -/
def machineBetheLineSumPayload (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Extract the word whose length bounds the line-sum accumulator. -/
def machineBetheLineSumBound (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Build the flattened-entry request for the current position in the line-sum scan. -/
def machineBetheLineSumEntryInput (state : List Bool) : List Bool :=
  let payload := machineBetheLineSumPayload state
  pair (machineBetheLineSumMode payload)
    (pair (machineBetheLineSumDimension payload)
      (pair (machineBetheLineSumFixed payload)
        (pair (machineBetheLineSumCurrent state)
          (machineBetheLineSumVector payload))))

/-- Evaluate the encoded raw-rational entry at the current scan position. -/
def machineBetheLineSumEntry (state : List Bool) : List Bool :=
  machineBetheFlatEntryRawCode (machineBetheLineSumEntryInput state)

/-- Add the current entry to the encoded line-sum accumulator. -/
def machineBetheLineSumCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineBetheLineSumAccumulator state)
      (machineBetheLineSumEntry state))

/-- Truncate the candidate accumulator code to the stored bound length. -/
def machineBetheLineSumNextAccumulator (state : List Bool) : List Bool :=
  (machineBetheLineSumCandidate state).take
    (machineBetheLineSumBound state).length

/-- Consume one remaining position, advance the unary index, and store the bounded updated sum. -/
def machineBetheLineSumAdvance (state : List Bool) : List Bool :=
  machineBetheLineSumPack
    (machineBetheLineSumRemaining state).tail
    (true :: machineBetheLineSumCurrent state)
    (machineBetheLineSumNextAccumulator state)
    (machineBetheLineSumPayload state)
    (machineBetheLineSumBound state)

/-- Leave a completed line-sum state unchanged, otherwise advance one position. -/
def machineBetheLineSumStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineBetheLineSumRemaining state) state
    (machineBetheLineSumAdvance state)

/-- Construct the line-sum bound word by applying the multiplication-width construction twice. -/
def machineBetheLineSumInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth word)

/-- Initialize the line-sum scan at index zero with a zero accumulator and the full dimension
ruler. -/
def machineBetheLineSumInit (word : List Bool) : List Bool :=
  machineBetheLineSumPack (machineBetheLineSumDimension word) []
    (rawRatBinaryCode RawRat.zero) word
    (machineBetheLineSumInputBound word)

/-- The packed width witness formed from five copies of the line-sum input bound word. -/
def machineBetheLineSumWidth (word : List Bool) : List Bool :=
  let bound := machineBetheLineSumInputBound word
  machineBetheLineSumPack bound bound bound bound bound

/-- Iterate the line-sum transition as many times as the dimension ruler length. -/
def machineBetheLineSumFinalState (word : List Bool) : List Bool :=
  (machineBetheLineSumStep)^[(machineBetheLineSumDimension word).length]
    (machineBetheLineSumInit word)

/-- Extract the raw-rational sum code from the final line-sum state. -/
def machineBetheLineSumRawCode (word : List Bool) : List Bool :=
  machineBetheLineSumAccumulator (machineBetheLineSumFinalState word)

theorem machineBetheLineSumMode_mem_FP : machineBetheLineSumMode ∈ FP :=
  machinePairFirst_mem_FP

theorem machineBetheLineSumRest_mem_FP : machineBetheLineSumRest ∈ FP :=
  machinePairSecond_mem_FP

theorem machineBetheLineSumDimension_mem_FP :
    machineBetheLineSumDimension ∈ FP := by
  simpa only [machineBetheLineSumDimension] using!
    machineCompose_mem_FP machineBetheLineSumRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheLineSumFixed_mem_FP :
    machineBetheLineSumFixed ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheLineSumRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheLineSumFixed] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheLineSumVector_mem_FP :
    machineBetheLineSumVector ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheLineSumRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheLineSumVector] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineBetheLineSumRemaining_mem_FP :
    machineBetheLineSumRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineBetheLineSumCurrent_mem_FP :
    machineBetheLineSumCurrent ∈ FP := by
  simpa only [machineBetheLineSumCurrent] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBetheLineSumAccumulator_mem_FP :
    machineBetheLineSumAccumulator ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheLineSumAccumulator] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheLineSumPayload_mem_FP :
    machineBetheLineSumPayload ∈ FP := by
  have htail₁ := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htail₂ := machineCompose_mem_FP htail₁ machinePairSecond_mem_FP
  simpa only [machineBetheLineSumPayload] using!
    machineCompose_mem_FP htail₂ machinePairFirst_mem_FP

theorem machineBetheLineSumBound_mem_FP :
    machineBetheLineSumBound ∈ FP := by
  have htail₁ := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htail₂ := machineCompose_mem_FP htail₁ machinePairSecond_mem_FP
  simpa only [machineBetheLineSumBound] using!
    machineCompose_mem_FP htail₂ machinePairSecond_mem_FP

theorem machineBetheLineSumEntryInput_mem_FP :
    machineBetheLineSumEntryInput ∈ FP := by
  have hmode := machineCompose_mem_FP machineBetheLineSumPayload_mem_FP
    machineBetheLineSumMode_mem_FP
  have hdim := machineCompose_mem_FP machineBetheLineSumPayload_mem_FP
    machineBetheLineSumDimension_mem_FP
  have hfixed := machineCompose_mem_FP machineBetheLineSumPayload_mem_FP
    machineBetheLineSumFixed_mem_FP
  have hvector := machineCompose_mem_FP machineBetheLineSumPayload_mem_FP
    machineBetheLineSumVector_mem_FP
  exact machinePair_mem_FP hmode
    (machinePair_mem_FP hdim
      (machinePair_mem_FP hfixed
        (machinePair_mem_FP machineBetheLineSumCurrent_mem_FP hvector)))

theorem machineBetheLineSumEntry_mem_FP : machineBetheLineSumEntry ∈ FP := by
  simpa only [machineBetheLineSumEntry] using!
    machineCompose_mem_FP machineBetheLineSumEntryInput_mem_FP
      machineBetheFlatEntryRawCode_mem_FP

theorem machineBetheLineSumCandidate_mem_FP :
    machineBetheLineSumCandidate ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheLineSumAccumulator_mem_FP
    machineBetheLineSumEntry_mem_FP
  simpa only [machineBetheLineSumCandidate] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineBetheLineSumNextAccumulator_mem_FP :
    machineBetheLineSumNextAccumulator ∈ FP := by
  simpa only [machineBetheLineSumNextAccumulator] using!
    machineTake_mem_FP machineBetheLineSumBound_mem_FP
      machineBetheLineSumCandidate_mem_FP

theorem machineBetheLineSumAdvance_mem_FP :
    machineBetheLineSumAdvance ∈ FP := by
  have hremaining := machineCompose_mem_FP
    machineBetheLineSumRemaining_mem_FP machineTail_mem_FP
  have hcurrent := machineCompose_mem_FP machineBetheLineSumCurrent_mem_FP
    (machinePrepend_mem_FP true)
  exact machinePair_mem_FP hremaining
    (machinePair_mem_FP hcurrent
      (machinePair_mem_FP machineBetheLineSumNextAccumulator_mem_FP
        (machinePair_mem_FP machineBetheLineSumPayload_mem_FP
          machineBetheLineSumBound_mem_FP)))

theorem machineBetheLineSumStep_mem_FP : machineBetheLineSumStep ∈ FP := by
  exact machineIfEmpty_mem_FP machineBetheLineSumRemaining_mem_FP
    id_mem_FP machineBetheLineSumAdvance_mem_FP

theorem machineBetheLineSumInputBound_mem_FP :
    machineBetheLineSumInputBound ∈ FP := by
  simpa only [machineBetheLineSumInputBound] using!
    machineCompose_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineBetheLineSumInit_mem_FP : machineBetheLineSumInit ∈ FP := by
  exact machinePair_mem_FP machineBetheLineSumDimension_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP
          (rawRatBinaryCode RawRat.zero))
        (machinePair_mem_FP id_mem_FP
          machineBetheLineSumInputBound_mem_FP)))

theorem machineBetheLineSumWidth_mem_FP : machineBetheLineSumWidth ∈ FP := by
  have h := machineBetheLineSumInputBound_mem_FP
  exact machinePair_mem_FP h
    (machinePair_mem_FP h (machinePair_mem_FP h (machinePair_mem_FP h h)))

@[simp] theorem machineBetheLineSumRemaining_pack (a b c d e) :
    machineBetheLineSumRemaining (machineBetheLineSumPack a b c d e) = a := by
  simp [machineBetheLineSumRemaining, machineBetheLineSumPack]

@[simp] theorem machineBetheLineSumCurrent_pack (a b c d e) :
    machineBetheLineSumCurrent (machineBetheLineSumPack a b c d e) = b := by
  simp [machineBetheLineSumCurrent, machineBetheLineSumPack]

@[simp] theorem machineBetheLineSumAccumulator_pack (a b c d e) :
    machineBetheLineSumAccumulator (machineBetheLineSumPack a b c d e) = c := by
  simp [machineBetheLineSumAccumulator, machineBetheLineSumPack]

@[simp] theorem machineBetheLineSumPayload_pack (a b c d e) :
    machineBetheLineSumPayload (machineBetheLineSumPack a b c d e) = d := by
  simp [machineBetheLineSumPayload, machineBetheLineSumPack]

@[simp] theorem machineBetheLineSumBound_pack (a b c d e) :
    machineBetheLineSumBound (machineBetheLineSumPack a b c d e) = e := by
  simp [machineBetheLineSumBound, machineBetheLineSumPack]

/-- The line-sum state invariant: canonical packing, bounded counters and payloads, and the
fixed input bound. -/
def MachineBetheLineSumStateBound (word state : List Bool) : Prop :=
  let B := (machineBetheLineSumInputBound word).length
  state = machineBetheLineSumPack
      (machineBetheLineSumRemaining state)
      (machineBetheLineSumCurrent state)
      (machineBetheLineSumAccumulator state)
      (machineBetheLineSumPayload state)
      (machineBetheLineSumBound state) ∧
    (machineBetheLineSumRemaining state).length +
        (machineBetheLineSumCurrent state).length ≤ B ∧
    (machineBetheLineSumAccumulator state).length ≤ B ∧
    (machineBetheLineSumPayload state).length ≤ B ∧
    machineBetheLineSumBound state = machineBetheLineSumInputBound word

theorem machineBetheLineSum_word_le_bound (word : List Bool) :
    word.length ≤ (machineBetheLineSumInputBound word).length := by
  simp only [machineBetheLineSumInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith [sq_nonneg (word.length + 16)]

theorem machineBetheLineSumInit_bound (word : List Bool) :
    MachineBetheLineSumStateBound word (machineBetheLineSumInit word) := by
  dsimp only [MachineBetheLineSumStateBound]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [machineBetheLineSumInit,
      machineBetheLineSumRemaining_pack,
      machineBetheLineSumCurrent_pack,
      machineBetheLineSumAccumulator_pack,
      machineBetheLineSumPayload_pack,
      machineBetheLineSumBound_pack]
  · simp only [machineBetheLineSumInit,
      machineBetheLineSumRemaining_pack,
      machineBetheLineSumCurrent_pack, List.length_nil, Nat.add_zero]
    exact (machinePairFirst_length_le (machineBetheLineSumRest word)).trans
      ((machinePairSecond_length_le word).trans
        (machineBetheLineSum_word_le_bound word))
  · simp only [machineBetheLineSumInit,
      machineBetheLineSumAccumulator_pack]
    exact (rawRatBinaryCode_length_le_width RawRat.zero).trans
      (by
        simp only [rawRatWidth_zero, machineBetheLineSumInputBound,
          machineBinaryMulWidth, List.length_replicate,
          List.length_append]
        nlinarith [sq_nonneg (word.length + 16)])
  · simpa only [machineBetheLineSumInit,
      machineBetheLineSumPayload_pack] using!
      machineBetheLineSum_word_le_bound word
  · simp only [machineBetheLineSumInit, machineBetheLineSumBound_pack]

theorem machineBetheLineSumStep_bound {word state : List Bool}
    (hs : MachineBetheLineSumStateBound word state) :
    MachineBetheLineSumStateBound word (machineBetheLineSumStep state) := by
  dsimp only [MachineBetheLineSumStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hindices, hacc, hpayload, hbound⟩
  by_cases hempty : machineBetheLineSumRemaining state = []
  · rw [machineBetheLineSumStep, hempty, machineIfEmpty_nil]
    exact ⟨hdecomp, hindices, hacc, hpayload, hbound⟩
  · cases hremaining : machineBetheLineSumRemaining state with
    | nil => exact False.elim (hempty hremaining)
    | cons bit tail =>
        rw [machineBetheLineSumStep, hremaining, machineIfEmpty_cons,
          machineBetheLineSumAdvance]
        simp only [machineBetheLineSumRemaining_pack,
          machineBetheLineSumCurrent_pack,
          machineBetheLineSumAccumulator_pack,
          machineBetheLineSumPayload_pack, machineBetheLineSumBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · have hsame :
              (machineBetheLineSumRemaining state).tail.length +
                  (true :: machineBetheLineSumCurrent state).length =
              (machineBetheLineSumRemaining state).length +
                  (machineBetheLineSumCurrent state).length := by
              rw [hremaining]
              simp only [List.tail_cons, List.length_cons]
              omega
          rw [hsame]
          exact hindices
        · rw [machineBetheLineSumNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineBetheLineSumIterate_bound (word : List Bool) : ∀ k,
    MachineBetheLineSumStateBound word
      ((machineBetheLineSumStep)^[k] (machineBetheLineSumInit word)) := by
  intro k
  induction k with
  | zero => exact machineBetheLineSumInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineBetheLineSumStep_bound ih

theorem machineBetheLineSumIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineBetheLineSumDimension word).length) :
    ((machineBetheLineSumStep)^[iterations]
      (machineBetheLineSumInit word)).length ≤
        (machineBetheLineSumWidth word).length := by
  rcases machineBetheLineSumIterate_bound word iterations with
    ⟨hdecomp, hindices, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineBetheLineSumPack, machineBetheLineSumWidth, pair_length]
  omega

theorem machineBetheLineSumFinalState_mem_FP :
    machineBetheLineSumFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineBetheLineSumStep_mem_FP
    machineBetheLineSumInit_mem_FP machineBetheLineSumDimension_mem_FP
    machineBetheLineSumWidth_mem_FP
    machineBetheLineSumIterate_length_le_width

theorem machineBetheLineSumRawCode_mem_FP :
    machineBetheLineSumRawCode ∈ FP := by
  simpa only [machineBetheLineSumRawCode] using!
    machineCompose_mem_FP machineBetheLineSumFinalState_mem_FP
      machineBetheLineSumAccumulator_mem_FP

/-! ## Exactness and absence of truncation on canonical inputs -/

/-- The canonical line-sum request encoding the mode, dimension, fixed index, and rational
vector. -/
def machineBetheLineSumCanonicalWord {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) : List Bool :=
  pair [rowMode]
    (pair (List.replicate m true)
      (pair (List.replicate fixed.1 true)
        (rationalFiniteVectorCode y)))

/-- List the free affine-coordinate values along the selected row or column. -/
def betheAffineLineValues {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) : List ℚ :=
  List.ofFn fun current : Fin m ↦
    if rowMode then y (finProdFinEquiv (fixed, current))
    else y (finProdFinEquiv (current, fixed))

/-- Sum the selected affine-coordinate row or column with raw-rational arithmetic. -/
def rawBetheAffineLineSum {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) : RawRat :=
  rawRatListSum RawRat.zero (betheAffineLineValues rowMode fixed y)

@[simp] theorem betheAffineLineValues_length {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    (betheAffineLineValues rowMode fixed y).length = m := by
  simp [betheAffineLineValues]

theorem betheLineSum_dimension_le_word {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    m ≤ (machineBetheLineSumCanonicalWord rowMode fixed y).length := by
  simp [machineBetheLineSumCanonicalWord]
  omega

theorem betheLineSum_vector_code_le_word {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    (rationalFiniteVectorCode y).length ≤
      (machineBetheLineSumCanonicalWord rowMode fixed y).length := by
  simp [machineBetheLineSumCanonicalWord]
  omega

theorem betheAffineLineValue_cost_le_word {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ)
    {q : ℚ} (hq : q ∈ betheAffineLineValues rowMode fixed y) :
    rawRatWidth (rawRatOfRat q) + 1 ≤
      (machineBetheLineSumCanonicalWord rowMode fixed y).length + 1 := by
  obtain ⟨current, rfl⟩ := List.mem_ofFn.mp hq
  let z : ℚ := if rowMode then y (finProdFinEquiv (fixed, current))
    else y (finProdFinEquiv (current, fixed))
  have hzmem : z ∈ List.ofFn y := by
    cases rowMode with
    | false =>
        simp only [z, Bool.false_eq_true, ite_false]
        exact (List.mem_ofFn).2 ⟨finProdFinEquiv (current, fixed), rfl⟩
    | true =>
        simp only [z, if_true]
        exact (List.mem_ofFn).2 ⟨finProdFinEquiv (fixed, current), rfl⟩
  have hentry := binaryListCode_element_length_le
    rationalEntryBinaryCode hzmem
  have hentry' : (rationalEntryBinaryCode z).length ≤
      (rationalFiniteVectorCode y).length := by
    simpa only [rationalFiniteVectorCode] using! hentry
  have hraw := rawRatWidth_le_binaryCode_length (rawRatOfRat z)
  rw [rawRatBinaryCode_rawRatOfRat] at hraw
  have hword := betheLineSum_vector_code_le_word rowMode fixed y
  change rawRatWidth (rawRatOfRat z) + 1 ≤ _
  omega

theorem rawRatListCost_betheLine_take_le {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) (k : ℕ) :
    rawRatListCost ((betheAffineLineValues rowMode fixed y).take k) ≤
      (machineBetheLineSumCanonicalWord rowMode fixed y).length *
        ((machineBetheLineSumCanonicalWord rowMode fixed y).length + 1) := by
  let values := betheAffineLineValues rowMode fixed y
  let W := (machineBetheLineSumCanonicalWord rowMode fixed y).length
  have heach : ∀ q ∈ values.take k,
      rawRatWidth (rawRatOfRat q) + 1 ≤ W + 1 := by
    intro q hq
    exact betheAffineLineValue_cost_le_word rowMode fixed y
      (List.mem_of_mem_take hq)
  have hsum := List.sum_le_card_nsmul
    ((values.take k).map fun q ↦ rawRatWidth (rawRatOfRat q) + 1)
    (W + 1) (by
      intro cost hcost
      rw [List.mem_map] at hcost
      obtain ⟨q, hq, rfl⟩ := hcost
      exact heach q hq)
  have hlength : (values.take k).length ≤ W := by
    have htake : (values.take k).length ≤ values.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    exact htake.trans
      (by simpa only [values, betheAffineLineValues_length, W] using!
        betheLineSum_dimension_le_word rowMode fixed y)
  have hlengthMap :
      ((values.take k).map
        fun q ↦ rawRatWidth (rawRatOfRat q) + 1).length ≤ W := by
    simpa only [List.length_map] using! hlength
  simp only [rawRatListCost]
  exact hsum.trans (Nat.mul_le_mul_right (W + 1) hlengthMap)

theorem rawBetheAffineLinePrefix_code_le_bound {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) (k : ℕ) :
    (rawRatBinaryCode
      (rawRatListSum RawRat.zero
        ((betheAffineLineValues rowMode fixed y).take k))).length ≤
      (machineBetheLineSumInputBound
        (machineBetheLineSumCanonicalWord rowMode fixed y)).length := by
  let word := machineBetheLineSumCanonicalWord rowMode fixed y
  let W := word.length
  let segment := (betheAffineLineValues rowMode fixed y).take k
  have hwidth := rawRatWidth_listSum_le RawRat.zero segment
  have hcost := rawRatListCost_betheLine_take_le rowMode fixed y k
  have hraw := rawRatBinaryCode_length_le_width
    (rawRatListSum RawRat.zero segment)
  have hwidth' : rawRatWidth (rawRatListSum RawRat.zero segment) ≤
      1 + W * (W + 1) := by
    simp only [rawRatWidth_zero] at hwidth
    simpa only [word, W, segment] using! hwidth.trans
      (Nat.add_le_add_left hcost 1)
  apply hraw.trans
  apply (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hwidth') 4).trans
  have hfirst : 4 + 3 * (1 + W * (W + 1)) ≤
      4 * (16 + W) ^ 2 := by nlinarith
  have hsecond : 4 * (16 + W) ^ 2 ≤
      (16 + (16 + W) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((16 + W) ^ 2)]
  apply hfirst.trans hsecond |>.trans_eq
  simp only [machineBetheLineSumInputBound, machineBinaryMulWidth,
    List.length_replicate, List.length_append, word, W, pow_two]

theorem rawRatListSum_append (acc : RawRat) : ∀ xs ys : List ℚ,
    rawRatListSum acc (xs ++ ys) =
      rawRatListSum (rawRatListSum acc xs) ys := by
  intro xs ys
  induction xs generalizing acc with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.cons_append, rawRatListSum]
      exact ih (acc.add (rawRatOfRat q))

theorem rawBetheAffineLinePrefix_succ {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) (k : ℕ) (hk : k < m) :
    rawRatListSum RawRat.zero
        ((betheAffineLineValues rowMode fixed y).take (k + 1)) =
      (rawRatListSum RawRat.zero
        ((betheAffineLineValues rowMode fixed y).take k)).add
          (rawRatOfRat
            (if rowMode then
              y (finProdFinEquiv (fixed, ⟨k, hk⟩))
            else y (finProdFinEquiv (⟨k, hk⟩, fixed)))) := by
  let values := betheAffineLineValues rowMode fixed y
  have hk' : k < values.length := by simpa only [values,
    betheAffineLineValues_length] using! hk
  have htake : values.take (k + 1) =
      values.take k ++ [values[k]] := by
    simpa only [List.concat_eq_append] using! (List.take_concat_get hk').symm
  rw [show (betheAffineLineValues rowMode fixed y).take (k + 1) =
      values.take (k + 1) by rfl, htake, rawRatListSum_append]
  simp only [rawRatListSum, List.getElem_ofFn, values,
    betheAffineLineValues]

/-- The semantic scan state after `k` positions, with the prefix sum and corresponding unary
counters. -/
def machineBetheLineSumSemanticState {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) (k : ℕ) : List Bool :=
  let word := machineBetheLineSumCanonicalWord rowMode fixed y
  machineBetheLineSumPack (List.replicate (m - k) true)
    (List.replicate k true)
    (rawRatBinaryCode
      (rawRatListSum RawRat.zero
        ((betheAffineLineValues rowMode fixed y).take k)))
    word (machineBetheLineSumInputBound word)

@[simp] theorem machineBetheLineSumMode_canonical {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumMode
        (machineBetheLineSumCanonicalWord rowMode fixed y) = [rowMode] := by
  simp [machineBetheLineSumMode, machineBetheLineSumCanonicalWord]

@[simp] theorem machineBetheLineSumDimension_canonical {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumDimension
        (machineBetheLineSumCanonicalWord rowMode fixed y) =
      List.replicate m true := by
  simp [machineBetheLineSumDimension, machineBetheLineSumRest,
    machineBetheLineSumCanonicalWord]

@[simp] theorem machineBetheLineSumFixed_canonical {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumFixed
        (machineBetheLineSumCanonicalWord rowMode fixed y) =
      List.replicate fixed.1 true := by
  simp [machineBetheLineSumFixed, machineBetheLineSumRest,
    machineBetheLineSumCanonicalWord]

@[simp] theorem machineBetheLineSumVector_canonical {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumVector
        (machineBetheLineSumCanonicalWord rowMode fixed y) =
      rationalFiniteVectorCode y := by
  simp [machineBetheLineSumVector, machineBetheLineSumRest,
    machineBetheLineSumCanonicalWord]

theorem machineBetheLineSumInit_semantics {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumInit
        (machineBetheLineSumCanonicalWord rowMode fixed y) =
      machineBetheLineSumSemanticState rowMode fixed y 0 := by
  simp [machineBetheLineSumInit, machineBetheLineSumSemanticState,
    rawRatListSum]

theorem machineBetheLineSumEntryInput_semantics {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ)
    (k : ℕ) (hk : k < m) :
    machineBetheLineSumEntryInput
        (machineBetheLineSumSemanticState rowMode fixed y k) =
      betheFlatIndexCanonicalWord rowMode fixed ⟨k, hk⟩ y := by
  simp [machineBetheLineSumEntryInput, machineBetheLineSumSemanticState,
    betheFlatIndexCanonicalWord]

theorem machineBetheLineSumStep_semantics {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ)
    (k : ℕ) (hk : k < m) :
    machineBetheLineSumStep
        (machineBetheLineSumSemanticState rowMode fixed y k) =
      machineBetheLineSumSemanticState rowMode fixed y (k + 1) := by
  let word := machineBetheLineSumCanonicalWord rowMode fixed y
  let segment := rawRatListSum RawRat.zero
    ((betheAffineLineValues rowMode fixed y).take k)
  let term := rawRatOfRat
    (if rowMode then y (finProdFinEquiv (fixed, ⟨k, hk⟩))
      else y (finProdFinEquiv (⟨k, hk⟩, fixed)))
  have hremaining : List.replicate (m - k) true =
      true :: List.replicate (m - (k + 1)) true := by
    have hsub : m - k = (m - (k + 1)) + 1 := by omega
    rw [hsub, List.replicate_succ]
  have hentryInput := machineBetheLineSumEntryInput_semantics
    rowMode fixed y k hk
  have hentry : machineBetheLineSumEntry
      (machineBetheLineSumSemanticState rowMode fixed y k) =
      rawRatBinaryCode term := by
    rw [machineBetheLineSumEntry, hentryInput,
      machineBetheFlatEntryRawCode_encode]
  have hentryPack : machineBetheLineSumEntry
      (machineBetheLineSumPack
        (true :: List.replicate (m - (k + 1)) true)
        (List.replicate k true) (rawRatBinaryCode segment) word
        (machineBetheLineSumInputBound word)) =
      rawRatBinaryCode term := by
    rw [← hremaining]
    simpa only [machineBetheLineSumSemanticState, word, segment] using! hentry
  have hprefix := rawBetheAffineLinePrefix_succ rowMode fixed y k hk
  have hcode : (rawRatBinaryCode (segment.add term)).length ≤
      (machineBetheLineSumInputBound word).length := by
    rw [show segment.add term = rawRatListSum RawRat.zero
        ((betheAffineLineValues rowMode fixed y).take (k + 1)) by
      exact hprefix.symm]
    exact rawBetheAffineLinePrefix_code_le_bound rowMode fixed y (k + 1)
  rw [machineBetheLineSumStep, machineBetheLineSumSemanticState,
    hremaining]
  simp only [machineBetheLineSumRemaining_pack, machineIfEmpty_cons,
    machineBetheLineSumAdvance, List.tail_cons,
    machineBetheLineSumCurrent_pack,
    machineBetheLineSumAccumulator_pack,
    machineBetheLineSumPayload_pack, machineBetheLineSumBound_pack,
    machineBetheLineSumNextAccumulator,
    machineBetheLineSumCandidate]
  change machineBetheLineSumPack
      (List.replicate (m - (k + 1)) true)
      (true :: List.replicate k true)
      ((machineRawRatAddCode
        (pair (rawRatBinaryCode segment)
          (machineBetheLineSumEntry
            (machineBetheLineSumPack
              (true :: List.replicate (m - (k + 1)) true)
              (List.replicate k true) (rawRatBinaryCode segment) word
              (machineBetheLineSumInputBound word))))).take
        (machineBetheLineSumInputBound word).length)
      word (machineBetheLineSumInputBound word) =
    machineBetheLineSumSemanticState rowMode fixed y (k + 1)
  rw [hentryPack, machineRawRatAddCode_encode]
  rw [(List.take_eq_self_iff _).mpr hcode]
  rw [show segment.add term = rawRatListSum RawRat.zero
      ((betheAffineLineValues rowMode fixed y).take (k + 1)) by
    exact hprefix.symm]
  simp only [machineBetheLineSumSemanticState, word,
    List.replicate_succ]

theorem machineBetheLineSumIterate_semantics {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) : ∀ k ≤ m,
    (machineBetheLineSumStep)^[k]
        (machineBetheLineSumInit
          (machineBetheLineSumCanonicalWord rowMode fixed y)) =
      machineBetheLineSumSemanticState rowMode fixed y k := by
  intro k hk
  induction k with
  | zero => exact machineBetheLineSumInit_semantics rowMode fixed y
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineBetheLineSumStep_semantics rowMode fixed y k (by omega)

@[simp] theorem machineBetheLineSumRawCode_encode {m : ℕ}
    (rowMode : Bool) (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    machineBetheLineSumRawCode
        (machineBetheLineSumCanonicalWord rowMode fixed y) =
      rawRatBinaryCode (rawBetheAffineLineSum rowMode fixed y) := by
  have hstate := congrArg machineBetheLineSumAccumulator
    (machineBetheLineSumIterate_semantics rowMode fixed y m le_rfl)
  have htake : (betheAffineLineValues rowMode fixed y).take m =
      betheAffineLineValues rowMode fixed y := by
    apply List.take_of_length_le
    simp
  simpa [machineBetheLineSumRawCode, machineBetheLineSumFinalState,
    machineBetheLineSumDimension_canonical,
    machineBetheLineSumSemanticState, rawBetheAffineLineSum, htake] using! hstate

theorem rawBetheAffineLineSum_value {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) :
    (rawBetheAffineLineSum rowMode fixed y).value =
      if rowMode then ∑ j : Fin m, y (finProdFinEquiv (fixed, j))
      else ∑ i : Fin m, y (finProdFinEquiv (i, fixed)) := by
  rw [rawBetheAffineLineSum, rawRatListSum_value,
    RawRat.value_zero, zero_add]
  cases rowMode <;> simp [betheAffineLineValues, List.sum_ofFn]

end BeyondBethe
