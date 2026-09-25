/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalRowDivide
public import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly
public import Mathlib.Tactic

/-!
# Entrywise normalization of a rational matrix

This machine computes `A / (1 + sum A)` entry by entry.  It preserves the
binary dimension prefix and maps the self-delimiting row list with the
verified row-division machine.  A polynomial clamp is present on malformed
inputs and is proved inactive on every canonical rational matrix.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Concatenates twenty copies of the input for the matrix-normalization width estimate. -/
def machineMatrixNormalizePadTwenty (word : List Bool) : List Bool :=
  machineRationalRowDividePadSixteen word ++
    machineRationalRowDividePadFour word

/-- A direct quadratic envelope in the original matrix-word length.  Using
twenty copies before squaring avoids materializing the much larger nested
row-machine envelope used in the first implementation. -/
def machineMatrixNormalizeInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineMatrixNormalizePadTwenty word)

/-- Encodes normalization state as remaining rows, reversed output, scale, dimension, and bound. -/
def machineMatrixNormalizePack
    (remaining accumulator scale dimension bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair scale (pair dimension bound)))

/-- Extracts the unprocessed rows from a matrix-normalization state. -/
def machineMatrixNormalizeRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the reversed accumulated normalized rows. -/
def machineMatrixNormalizeAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the fixed raw-rational normalization scale. -/
def machineMatrixNormalizeScale (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the binary dimension retained in the normalization state. -/
def machineMatrixNormalizeDimension (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Extracts the stored width bound from the normalization state. -/
def machineMatrixNormalizeBound (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Reads the first unprocessed row to normalize. -/
def machineMatrixNormalizeCurrentRow (state : List Bool) : List Bool :=
  machineListHead (machineMatrixNormalizeRemaining state)

/-- Divides every entry of the current row by the stored normalization scale. -/
def machineMatrixNormalizeOutputRow (state : List Bool) : List Bool :=
  machineRationalRowDivide
    (pair (machineMatrixNormalizeScale state)
      (machineMatrixNormalizeCurrentRow state))

/-- Prepends the normalized current row to the reversed output accumulator. -/
def machineMatrixNormalizeCandidate (state : List Bool) : List Bool :=
  pair (machineMatrixNormalizeOutputRow state)
    (machineMatrixNormalizeAccumulator state)

/-- Truncates the candidate normalized-row accumulator to the stored width bound. -/
def machineMatrixNormalizeNextAccumulator (state : List Bool) : List Bool :=
  (machineMatrixNormalizeCandidate state).take
    (machineMatrixNormalizeBound state).length

/-- Consumes one row and stores its normalized output while preserving scale, dimension, and
bound. -/
def machineMatrixNormalizeAdvance (state : List Bool) : List Bool :=
  machineMatrixNormalizePack
    (machineListTail (machineMatrixNormalizeRemaining state))
    (machineMatrixNormalizeNextAccumulator state)
    (machineMatrixNormalizeScale state)
    (machineMatrixNormalizeDimension state)
    (machineMatrixNormalizeBound state)

/-- Normalizes the next row, leaving exhausted normalization states fixed. -/
def machineMatrixNormalizeStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixNormalizeRemaining state) state
    (machineMatrixNormalizeAdvance state)

/-- Initializes normalization with the source rows, empty output, computed scale, dimension, and
bound. -/
def machineMatrixNormalizeInit (word : List Bool) : List Bool :=
  machineMatrixNormalizePack (machineMatrixRowsWord word) []
    (machineMatrixNormalizationScaleRawCode word)
    (machineMatrixDimensionWord word)
    (machineMatrixNormalizeInputBound word)

/-- Builds an encoded width envelope for the five normalization-state components. -/
def machineMatrixNormalizeWidth (word : List Bool) : List Bool :=
  machineMatrixNormalizePack word (machineMatrixNormalizeInputBound word)
    (machineMatrixNormalizationScaleRawCode word) word
    (machineMatrixNormalizeInputBound word)

/-- Runs matrix normalization for one step per input bit. -/
def machineMatrixNormalizeFinalState (word : List Bool) : List Bool :=
  (machineMatrixNormalizeStep)^[word.length]
    (machineMatrixNormalizeInit word)

/-- Pairs the matrix dimension with normalized rows restored to their original order. -/
def machineMatrixNormalizeEntries (word : List Bool) : List Bool :=
  let state := machineMatrixNormalizeFinalState word
  pair (machineMatrixNormalizeDimension state)
    (machineListReverse (machineMatrixNormalizeAccumulator state))

theorem machineMatrixNormalizePadTwenty_mem_FP :
    machineMatrixNormalizePadTwenty ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowDividePadSixteen_mem_FP
    machineRationalRowDividePadFour_mem_FP

theorem machineMatrixNormalizePadTwenty_length (word : List Bool) :
    (machineMatrixNormalizePadTwenty word).length = 20 * word.length := by
  simp only [machineMatrixNormalizePadTwenty, List.length_append,
    machineRationalRowDividePadSixteen_length,
    machineRationalRowDividePadFour,
    machineRationalRowDividePadTwo, List.length_append]
  omega

theorem machineMatrixNormalizeInputBound_mem_FP :
    machineMatrixNormalizeInputBound ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizeInputBound] using!
    machineCompose_mem_FP machineMatrixNormalizePadTwenty_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineMatrixNormalizeRemaining_mem_FP :
    machineMatrixNormalizeRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineMatrixNormalizeAccumulator_mem_FP :
    machineMatrixNormalizeAccumulator ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizeAccumulator] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatrixNormalizeScale_mem_FP :
    machineMatrixNormalizeScale ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineMatrixNormalizeScale] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineMatrixNormalizeDimension_mem_FP :
    machineMatrixNormalizeDimension ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineMatrixNormalizeDimension] using!
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineMatrixNormalizeBound_mem_FP :
    machineMatrixNormalizeBound ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineMatrixNormalizeBound] using!
    machineCompose_mem_FP htailThree machinePairSecond_mem_FP

theorem machineMatrixNormalizeCurrentRow_mem_FP :
    machineMatrixNormalizeCurrentRow ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizeCurrentRow] using!
    machineCompose_mem_FP machineMatrixNormalizeRemaining_mem_FP
      machineListHead_mem_FP

theorem machineMatrixNormalizeOutputRow_mem_FP :
    machineMatrixNormalizeOutputRow ∈ Complexity.FP := by
  have hinput := machinePair_mem_FP machineMatrixNormalizeScale_mem_FP
    machineMatrixNormalizeCurrentRow_mem_FP
  simpa only [machineMatrixNormalizeOutputRow] using!
    machineCompose_mem_FP hinput machineRationalRowDivide_mem_FP

theorem machineMatrixNormalizeCandidate_mem_FP :
    machineMatrixNormalizeCandidate ∈ Complexity.FP :=
  machinePair_mem_FP machineMatrixNormalizeOutputRow_mem_FP
    machineMatrixNormalizeAccumulator_mem_FP

theorem machineMatrixNormalizeNextAccumulator_mem_FP :
    machineMatrixNormalizeNextAccumulator ∈ Complexity.FP := by
  simpa only [machineMatrixNormalizeNextAccumulator] using!
    machineTake_mem_FP machineMatrixNormalizeBound_mem_FP
      machineMatrixNormalizeCandidate_mem_FP

theorem machineMatrixNormalizeAdvance_mem_FP :
    machineMatrixNormalizeAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixNormalizeRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineMatrixNormalizeNextAccumulator_mem_FP
      (machinePair_mem_FP machineMatrixNormalizeScale_mem_FP
        (machinePair_mem_FP machineMatrixNormalizeDimension_mem_FP
          machineMatrixNormalizeBound_mem_FP)))

theorem machineMatrixNormalizeStep_mem_FP :
    machineMatrixNormalizeStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixNormalizeRemaining_mem_FP
    id_mem_FP machineMatrixNormalizeAdvance_mem_FP

theorem machineMatrixNormalizeInit_mem_FP :
    machineMatrixNormalizeInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixRowsWord_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineMatrixNormalizationScaleRawCode_mem_FP
        (machinePair_mem_FP machineMatrixDimensionWord_mem_FP
          machineMatrixNormalizeInputBound_mem_FP)))

theorem machineMatrixNormalizeWidth_mem_FP :
    machineMatrixNormalizeWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineMatrixNormalizeInputBound_mem_FP
      (machinePair_mem_FP machineMatrixNormalizationScaleRawCode_mem_FP
        (machinePair_mem_FP id_mem_FP
          machineMatrixNormalizeInputBound_mem_FP)))

@[simp] theorem machineMatrixNormalizeRemaining_pack (a b c d e) :
    machineMatrixNormalizeRemaining
      (machineMatrixNormalizePack a b c d e) = a := by
  simp [machineMatrixNormalizeRemaining, machineMatrixNormalizePack]

@[simp] theorem machineMatrixNormalizeAccumulator_pack (a b c d e) :
    machineMatrixNormalizeAccumulator
      (machineMatrixNormalizePack a b c d e) = b := by
  simp [machineMatrixNormalizeAccumulator, machineMatrixNormalizePack]

@[simp] theorem machineMatrixNormalizeScale_pack (a b c d e) :
    machineMatrixNormalizeScale
      (machineMatrixNormalizePack a b c d e) = c := by
  simp [machineMatrixNormalizeScale, machineMatrixNormalizePack]

@[simp] theorem machineMatrixNormalizeDimension_pack (a b c d e) :
    machineMatrixNormalizeDimension
      (machineMatrixNormalizePack a b c d e) = d := by
  simp [machineMatrixNormalizeDimension, machineMatrixNormalizePack]

@[simp] theorem machineMatrixNormalizeBound_pack (a b c d e) :
    machineMatrixNormalizeBound
      (machineMatrixNormalizePack a b c d e) = e := by
  simp [machineMatrixNormalizeBound, machineMatrixNormalizePack]

/-- Bounds normalization state lengths and preserves the computed scale and input-derived bound. -/
def MachineMatrixNormalizeStateBound (word state : List Bool) : Prop :=
  state = machineMatrixNormalizePack
      (machineMatrixNormalizeRemaining state)
      (machineMatrixNormalizeAccumulator state)
      (machineMatrixNormalizeScale state)
      (machineMatrixNormalizeDimension state)
      (machineMatrixNormalizeBound state) ∧
    (machineMatrixNormalizeRemaining state).length ≤ word.length ∧
    (machineMatrixNormalizeAccumulator state).length ≤
      (machineMatrixNormalizeInputBound word).length ∧
    machineMatrixNormalizeScale state =
      machineMatrixNormalizationScaleRawCode word ∧
    (machineMatrixNormalizeDimension state).length ≤ word.length ∧
    machineMatrixNormalizeBound state = machineMatrixNormalizeInputBound word

theorem machineMatrixNormalizeInit_bound (word : List Bool) :
    MachineMatrixNormalizeStateBound word (machineMatrixNormalizeInit word) := by
  simp only [MachineMatrixNormalizeStateBound, machineMatrixNormalizeInit,
    machineMatrixNormalizeRemaining_pack,
    machineMatrixNormalizeAccumulator_pack,
    machineMatrixNormalizeScale_pack,
    machineMatrixNormalizeDimension_pack,
    machineMatrixNormalizeBound_pack]
  refine ⟨trivial, ?_, by simp, trivial, ?_, trivial⟩
  · simpa only [machineMatrixRowsWord] using! machinePairSecond_length_le word
  · simpa only [machineMatrixDimensionWord] using!
      machinePairFirst_length_le word

theorem machineMatrixNormalizeStep_bound {word state : List Bool}
    (hstate : MachineMatrixNormalizeStateBound word state) :
    MachineMatrixNormalizeStateBound word
      (machineMatrixNormalizeStep state) := by
  rcases hstate with
    ⟨hdecomp, hremaining, haccumulator, hscale, hdimension, hbound⟩
  by_cases hnil : machineMatrixNormalizeRemaining state = []
  · rw [machineMatrixNormalizeStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, haccumulator, hscale, hdimension, hbound⟩
  · rw [machineMatrixNormalizeStep]
    cases hremainingCode : machineMatrixNormalizeRemaining state with
    | nil => exact False.elim (hnil hremainingCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixNormalizeAdvance]
        simp only [MachineMatrixNormalizeStateBound,
          machineMatrixNormalizeRemaining_pack,
          machineMatrixNormalizeAccumulator_pack,
          machineMatrixNormalizeScale_pack,
          machineMatrixNormalizeDimension_pack,
          machineMatrixNormalizeBound_pack]
        refine ⟨trivial, ?_, ?_, hscale, hdimension, hbound⟩
        · exact (machineListTail_length_le
            (machineMatrixNormalizeRemaining state)).trans hremaining
        · rw [machineMatrixNormalizeNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineMatrixNormalizeIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixNormalizeStateBound word
      ((machineMatrixNormalizeStep)^[k]
        (machineMatrixNormalizeInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixNormalizeInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixNormalizeStep_bound ih

theorem machineMatrixNormalizeIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineMatrixNormalizeStep)^[iterations]
      (machineMatrixNormalizeInit word)).length ≤
        (machineMatrixNormalizeWidth word).length := by
  rcases machineMatrixNormalizeIterate_bound word iterations with
    ⟨hdecomp, hremaining, haccumulator, hscale, hdimension, hbound⟩
  rw [hdecomp, hscale, hbound]
  simp only [machineMatrixNormalizePack, machineMatrixNormalizeWidth,
    pair_length]
  omega

theorem machineMatrixNormalizeFinalState_mem_FP :
    machineMatrixNormalizeFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixNormalizeStep_mem_FP
    machineMatrixNormalizeInit_mem_FP id_mem_FP
    machineMatrixNormalizeWidth_mem_FP
    machineMatrixNormalizeIterate_length_le_width

theorem machineMatrixNormalizeEntries_mem_FP :
    machineMatrixNormalizeEntries ∈ Complexity.FP := by
  have hdimension := machineCompose_mem_FP
    machineMatrixNormalizeFinalState_mem_FP
    machineMatrixNormalizeDimension_mem_FP
  have hacc := machineCompose_mem_FP
    machineMatrixNormalizeFinalState_mem_FP
    machineMatrixNormalizeAccumulator_mem_FP
  have hrows := machineCompose_mem_FP hacc machineListReverse_mem_FP
  simpa only [machineMatrixNormalizeEntries] using!
    machinePair_mem_FP hdimension hrows

/-! ## Output-size bound on canonical matrices -/

private theorem matrixNormalize_natList_sum_le_length_mul
    {values : List ℕ} {bound : ℕ}
    (h : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      have hvalue := h value (by simp)
      have htail : ∀ x ∈ values, x ≤ bound := by
        intro x hx
        exact h x (by simp [hx])
      have hi := ih htail
      calc
        value + values.sum ≤ bound + values.length * bound :=
          Nat.add_le_add hvalue hi
        _ = (values.length + 1) * bound := by ring

private theorem matrixNonnegativeRowsWork_eq_length_add_entries :
    ∀ rows : List (List ℚ),
      matrixNonnegativeRowsWork rows =
        rows.length + (rows.map List.length).sum := by
  intro rows
  induction rows with
  | nil => simp [matrixNonnegativeRowsWork]
  | cons row rows ih =>
      simp [matrixNonnegativeRowsWork, ih]
      omega

private theorem matrixNormalize_outputCode_length_le
    (scale : RawRat) (budget : ℕ) : ∀ rows : List (List ℚ),
    (∀ row ∈ rows, ∀ q ∈ row,
      (rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat q).div scale))).length ≤
          172 + 72 * budget) →
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rows.map (rationalRowDivideValues scale))).length ≤
      (rows.map List.length).sum * (692 + 288 * budget) +
        2 * rows.length := by
  intro rows hentry
  induction rows with
  | nil => simp [binaryListCode]
  | cons row rows ih =>
      have hrowEntry : ∀ q ∈ row,
          (rationalEntryBinaryCode
            (binaryNormalizeRawRat ((rawRatOfRat q).div scale))).length ≤
              172 + 72 * budget := by
        intro q hq
        exact hentry row (by simp) q hq
      have htailEntry : ∀ tailRow ∈ rows, ∀ q ∈ tailRow,
          (rationalEntryBinaryCode
            (binaryNormalizeRawRat ((rawRatOfRat q).div scale))).length ≤
              172 + 72 * budget := by
        intro tailRow htailRow q hq
        exact hentry tailRow (by simp [htailRow]) q hq
      have hinner :
          (binaryListCode rationalEntryBinaryCode
            (rationalRowDivideValues scale row)).length ≤
              row.length * (346 + 144 * budget) := by
        rw [binaryListCode_length_eq_sum]
        have hterm : ∀ value ∈
            ((rationalRowDivideValues scale row).map
              fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2),
            value ≤ 346 + 144 * budget := by
          simp only [rationalRowDivideValues, List.map_map]
          intro value hvalue
          rw [List.mem_map] at hvalue
          rcases hvalue with ⟨q, hq, rfl⟩
          have hqBound := hrowEntry q hq
          simp only [Function.comp_apply]
          omega
        have hsum := matrixNormalize_natList_sum_le_length_mul hterm
        simpa only [rationalRowDivideValues, List.length_map] using! hsum
      have htail := ih htailEntry
      simp only [List.map_cons, binaryListCode, pair_length,
        List.map_map, List.sum_cons, List.length_cons] at htail ⊢
      nlinarith

theorem machineMatrixNormalize_outputRows_length_le_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
    let scale := RawRat.one.add
      (rawRatRowsSum RawRat.zero (rationalMatrixRows A))
    let output := (rationalMatrixRows A).map
      (rationalRowDivideValues scale)
    (binaryListCode (binaryListCode rationalEntryBinaryCode) output).length ≤
      (machineMatrixNormalizeInputBound word).length := by
  dsimp only
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let rows := rationalMatrixRows A
  let scale := RawRat.one.add (rawRatRowsSum RawRat.zero rows)
  have hrowsCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machineMatrixRowsWord word).length := by
        simpa only [word, rows] using! congrArg List.length
          (machineMatrixRowsWord_encode A).symm
      _ ≤ word.length := by
        simpa only [machineMatrixRowsWord] using!
          machinePairSecond_length_le word
  have hcost : rawRatRowsCost rows ≤ word.length :=
    (rawRatRowsCost_le_codeLength rows).trans hrowsCode
  have hsumWidth :
      rawRatWidth (rawRatRowsSum RawRat.zero rows) ≤ 1 + word.length := by
    have h := rawRatWidth_rowsSum_le RawRat.zero rows
    simpa only [rawRatWidth_zero] using! h.trans
      (Nat.add_le_add_left hcost 1)
  have hscaleWidth : rawRatWidth scale ≤ word.length + 3 := by
    have h := rawRatWidth_add_le RawRat.one
      (rawRatRowsSum RawRat.zero rows)
    simp only [rawRatWidth_one] at h
    have hraw :
        rawRatWidth
            (RawRat.one.add (rawRatRowsSum RawRat.zero rows)) ≤
          word.length + 3 := by
      omega
    simpa only [scale] using! hraw
  have hentry : ∀ row ∈ rows, ∀ q ∈ row,
      (rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat q).div scale))).length ≤
          172 + 72 * word.length := by
    intro row hrow q hq
    have hqCode := binaryListCode_element_length_le
      rationalEntryBinaryCode hq
    have hrowCode := binaryListCode_element_length_le
      (binaryListCode rationalEntryBinaryCode) hrow
    have hqWidth : rawRatWidth (rawRatOfRat q) ≤ word.length := by
      have hentryCode :
          (rawRatBinaryCode (rawRatOfRat q)).length ≤ word.length := by
        rw [rawRatBinaryCode_rawRatOfRat]
        exact hqCode.trans (hrowCode.trans hrowsCode)
      exact (rawRatWidth_le_binaryCode_length (rawRatOfRat q)).trans
        hentryCode
    have hdiv := rawRatWidth_div_le (rawRatOfRat q) scale
    have hnormalize :=
      rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
        ((rawRatOfRat q).div scale)
    omega
  have houtput := matrixNormalize_outputCode_length_le
    scale word.length rows hentry
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsCode
  rw [matrixNonnegativeRowsWork_eq_length_add_entries] at hwork
  have hquadratic :
      (rows.map List.length).sum * (692 + 288 * word.length) +
          2 * rows.length ≤
        (machineMatrixNormalizeInputBound word).length := by
    rw [machineMatrixNormalizeInputBound]
    simp only [machineBinaryMulWidth, List.length_replicate,
      List.length_append]
    rw [machineMatrixNormalizePadTwenty_length]
    have hcombined :
        (rows.map List.length).sum * (692 + 288 * word.length) +
            2 * rows.length ≤
          (rows.length + (rows.map List.length).sum) *
            (694 + 288 * word.length) := by
      have hentries := Nat.mul_le_mul_left
        (rows.map List.length).sum
        (show 692 + 288 * word.length ≤ 694 + 288 * word.length by omega)
      have hrows := Nat.mul_le_mul_left rows.length
        (show 2 ≤ 694 + 288 * word.length by omega)
      calc
        (rows.map List.length).sum * (692 + 288 * word.length) +
              2 * rows.length ≤
            (rows.map List.length).sum * (694 + 288 * word.length) +
              rows.length * (694 + 288 * word.length) := by
                exact Nat.add_le_add hentries (by simpa [Nat.mul_comm] using! hrows)
        _ = (rows.length + (rows.map List.length).sum) *
              (694 + 288 * word.length) := by ring
    have hlinear := Nat.mul_le_mul_right (694 + 288 * word.length) hwork
    have hsquare :
        word.length * (694 + 288 * word.length) ≤
          (16 + 20 * word.length) * (16 + 20 * word.length) := by
      cases hword : word.length with
      | zero => simp
      | succ length =>
          have hsquareDominates : length + 1 ≤ (length + 1) * (length + 1) := by
            nlinarith
          nlinarith
    exact hcombined.trans (hlinear.trans hsquare)
  exact houtput.trans hquadratic

/-! ## Exact semantics -/

/-- Divides every entry of every supplied row by the raw-rational scale. -/
def rationalMatrixDivideRows (scale : RawRat)
    (rows : List (List ℚ)) : List (List ℚ) :=
  rows.map (rationalRowDivideValues scale)

/-- Encodes normalization after `k` rows, with the remaining input rows and reversed normalized
output. -/
def machineMatrixNormalizeSemanticState
    (word dimension : List Bool) (scale : RawRat)
    (rows : List (List ℚ)) (k : ℕ) : List Bool :=
  let output := rationalMatrixDivideRows scale rows
  machineMatrixNormalizePack
    (binaryListCode (binaryListCode rationalEntryBinaryCode) (rows.drop k))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (output.take k).reverse)
    (rawRatBinaryCode scale) dimension
    (machineMatrixNormalizeInputBound word)

theorem machineMatrixNormalizeInit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
    let scale := RawRat.one.add
      (rawRatRowsSum RawRat.zero (rationalMatrixRows A))
    machineMatrixNormalizeInit word =
      machineMatrixNormalizeSemanticState word n.bits scale
        (rationalMatrixRows A) 0 := by
  dsimp only
  rw [machineMatrixNormalizeInit]
  simp only [machineMatrixRowsWord_encode,
    machineMatrixNormalizationScaleRawCode_encode,
    machineMatrixDimensionWord_encode,
    machineMatrixNormalizeSemanticState, List.drop_zero,
    List.take_zero, List.reverse_nil, binaryListCode]

theorem machineMatrixNormalizeOutputRow_semantics
    (word dimension : List Bool) (scale : RawRat)
    (rows : List (List ℚ)) (k : ℕ) (hk : k < rows.length) :
    machineMatrixNormalizeOutputRow
        (machineMatrixNormalizeSemanticState word dimension scale rows k) =
      binaryListCode rationalEntryBinaryCode
        (rationalRowDivideValues scale rows[k]) := by
  have hdrop := List.drop_eq_getElem_cons hk
  rw [machineMatrixNormalizeOutputRow]
  simp only [machineMatrixNormalizeSemanticState,
    machineMatrixNormalizeScale_pack,
    machineMatrixNormalizeCurrentRow,
    machineMatrixNormalizeRemaining_pack, hdrop,
    machineListHead_cons]
  change machineRationalRowDivide
      (machineRationalRowDivideCanonicalInput scale rows[k]) = _
  exact machineRationalRowDivide_encode scale rows[k]

theorem machineMatrixNormalizeStep_semantics
    (word dimension : List Bool) (scale : RawRat)
    (rows : List (List ℚ)) (k : ℕ) (hk : k < rows.length)
    (hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixDivideRows scale rows)).length ≤
          (machineMatrixNormalizeInputBound word).length) :
    machineMatrixNormalizeStep
        (machineMatrixNormalizeSemanticState word dimension scale rows k) =
      machineMatrixNormalizeSemanticState word dimension scale rows (k + 1) := by
  let output := rationalMatrixDivideRows scale rows
  have houtputLength : output.length = rows.length := by
    simp [output, rationalMatrixDivideRows]
  have hkoutput : k < output.length := by omega
  have houtputGet : output[k] =
      rationalRowDivideValues scale rows[k] := by
    simp [output, rationalMatrixDivideRows, List.getElem_map]
  have hdrop := List.drop_eq_getElem_cons hk
  have htake := List.take_concat_get hkoutput
  have hprefix : (output.take (k + 1)).reverse =
      output[k] :: (output.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := output.take k) (a := output[k]))
  have hprefixLength :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (output.take (k + 1)).reverse).length ≤
          (machineMatrixNormalizeInputBound word).length :=
    (binaryListCode_take_reverse_length_le
      (binaryListCode rationalEntryBinaryCode) output (k + 1)).trans
        (by simpa only [output] using! hfullBound)
  have htakeBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (output.take (k + 1)).reverse).take
            (machineMatrixNormalizeInputBound word).length =
        binaryListCode (binaryListCode rationalEntryBinaryCode)
          (output.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hnonempty :
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rows.drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil _ _ _
  rw [machineMatrixNormalizeStep]
  simp only [machineMatrixNormalizeSemanticState,
    machineMatrixNormalizeRemaining_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hnonempty,
    machineMatrixNormalizeAdvance]
  simp only [machineMatrixNormalizeRemaining_pack,
    machineMatrixNormalizeAccumulator_pack,
    machineMatrixNormalizeScale_pack,
    machineMatrixNormalizeDimension_pack,
    machineMatrixNormalizeBound_pack,
    machineMatrixNormalizeNextAccumulator,
    machineMatrixNormalizeCandidate]
  have hrow :
      machineMatrixNormalizeOutputRow
          (machineMatrixNormalizePack
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              (rows.drop k))
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              (output.take k).reverse)
            (rawRatBinaryCode scale) dimension
            (machineMatrixNormalizeInputBound word)) =
        binaryListCode rationalEntryBinaryCode output[k] := by
    rw [houtputGet]
    simpa only [machineMatrixNormalizeSemanticState, output] using!
      machineMatrixNormalizeOutputRow_semantics
        word dimension scale rows k hk
  rw [hrow, hdrop, machineListTail_cons]
  change machineMatrixNormalizePack
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rows.drop (k + 1)))
      ((binaryListCode (binaryListCode rationalEntryBinaryCode)
        (output[k] :: (output.take k).reverse)).take
          (machineMatrixNormalizeInputBound word).length)
      (rawRatBinaryCode scale) dimension
      (machineMatrixNormalizeInputBound word) = _
  rw [← hprefix, htakeBound]

theorem machineMatrixNormalizeIterate_semantics
    (word dimension : List Bool) (scale : RawRat)
    (rows : List (List ℚ))
    (hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixDivideRows scale rows)).length ≤
          (machineMatrixNormalizeInputBound word).length) : ∀ k ≤ rows.length,
    (machineMatrixNormalizeStep)^[k]
        (machineMatrixNormalizeSemanticState word dimension scale rows 0) =
      machineMatrixNormalizeSemanticState word dimension scale rows k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineMatrixNormalizeStep_semantics word dimension scale rows k
        (by omega) hfullBound

theorem machineMatrixNormalize_done_iterate
    (extra : ℕ) (accumulator scale dimension bound : List Bool) :
    (machineMatrixNormalizeStep)^[extra]
        (machineMatrixNormalizePack [] accumulator scale dimension bound) =
      machineMatrixNormalizePack [] accumulator scale dimension bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineMatrixNormalizeStep]

theorem machineMatrixNormalizeFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
    let rows := rationalMatrixRows A
    let scale := RawRat.one.add (rawRatRowsSum RawRat.zero rows)
    machineMatrixNormalizeFinalState word =
      machineMatrixNormalizePack []
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixDivideRows scale rows).reverse)
        (rawRatBinaryCode scale) n.bits
        (machineMatrixNormalizeInputBound word) := by
  dsimp only
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let rows := rationalMatrixRows A
  let scale := RawRat.one.add (rawRatRowsSum RawRat.zero rows)
  have hrowsLength : rows.length ≤ word.length := by
    simpa only [rows, word, rationalMatrixRows, List.length_ofFn] using!
      matrix_dimension_le_code_length A
  have hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixDivideRows scale rows)).length ≤
          (machineMatrixNormalizeInputBound word).length := by
    simpa only [word, rows, scale, rationalMatrixDivideRows] using!
      machineMatrixNormalize_outputRows_length_le_bound A
  have hsplit : word.length =
      (word.length - rows.length) + rows.length := by omega
  have htakeAll :
      (rationalMatrixDivideRows scale rows).take rows.length =
        rationalMatrixDivideRows scale rows := by
    have hlength : (rationalMatrixDivideRows scale rows).length =
        rows.length := by simp [rationalMatrixDivideRows]
    rw [← hlength, List.take_length]
  change (machineMatrixNormalizeStep)^[word.length]
      (machineMatrixNormalizeInit word) = _
  rw [hsplit, Function.iterate_add_apply,
    machineMatrixNormalizeInit_encode A,
    machineMatrixNormalizeIterate_semantics word n.bits scale rows
      hfullBound rows.length le_rfl]
  simp only [machineMatrixNormalizeSemanticState, List.drop_length,
    binaryListCode]
  rw [htakeAll, machineMatrixNormalize_done_iterate]

theorem rationalMatrixDivideRows_normalized {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let rows := rationalMatrixRows A
    let scale := RawRat.one.add (rawRatRowsSum RawRat.zero rows)
    rationalMatrixDivideRows scale rows =
      rationalMatrixRows (normalizedRationalMatrix A) := by
  dsimp only
  have hscale :
      (RawRat.one.add
        (rawRatRowsSum RawRat.zero (rationalMatrixRows A))).value =
          rationalNormalizationScale A := by
    rw [RawRat.value_add, RawRat.value_one, rawRatRowsSum_value,
      RawRat.value_zero, zero_add, rationalMatrixRows_sum]
    rfl
  have hscaleRows := hscale
  simp only [rationalMatrixRows] at hscaleRows
  apply List.ext_get
  · simp [rationalMatrixDivideRows, rationalMatrixRows]
  · intro i hi hi'
    apply List.ext_get
    · simp [rationalMatrixDivideRows, rationalRowDivideValues,
        rationalMatrixRows]
    · intro j hj hj'
      simp [rationalMatrixDivideRows, rationalRowDivideValues,
        rationalMatrixRows, normalizedRationalMatrix,
        binaryNormalizeRawRat_eq_value, RawRat.value_div,
        rawRatOfRat_value, hscaleRows]

@[simp] theorem machineMatrixNormalizeEntries_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNormalizeEntries
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, normalizedRationalMatrix A⟩ := by
  let rows := rationalMatrixRows A
  let scale := RawRat.one.add (rawRatRowsSum RawRat.zero rows)
  rw [machineMatrixNormalizeEntries,
    machineMatrixNormalizeFinalState_encode A]
  simp only [machineMatrixNormalizeDimension_pack,
    machineMatrixNormalizeAccumulator_pack,
    machineListReverse_encode, List.reverse_reverse]
  rw [rationalMatrixDivideRows_normalized A]
  rfl

end BeyondBethe
