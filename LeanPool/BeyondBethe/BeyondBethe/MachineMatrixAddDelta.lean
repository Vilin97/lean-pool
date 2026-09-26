/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalRowAdd
public import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly
public import Mathlib.Tactic

/-!
# Entrywise addition of a rational matrix

The input is `pair deltaRawCode matrixCode`.  The machine adds `delta` to
every entry, preserves the matrix dimension prefix, and maps the
self-delimiting row list with the verified row-addition machine.  A
polynomial clamp is present on malformed inputs and is proved inactive on
every canonical pair of a raw rational and a rational matrix.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the encoded rational increment from the matrix-addition input. -/
def machineMatrixAddDeltaInputDelta (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the encoded matrix from the matrix-addition input. -/
def machineMatrixAddDeltaInputMatrix (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Concatenates twenty copies of the input for the matrix-addition width estimate. -/
def machineMatrixAddDeltaPadTwenty (word : List Bool) : List Bool :=
  machineRationalRowAddPadSixteen word ++
    machineRationalRowAddPadFour word

/-- A direct quadratic envelope in the original matrix-word length.  Using
twenty copies before squaring avoids materializing the much larger nested
row-machine envelope used in the first implementation. -/
def machineMatrixAddDeltaInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineMatrixAddDeltaPadTwenty word)

/-- Encodes matrix-addition state as remaining rows, reversed output, increment, dimension, and
bound. -/
def machineMatrixAddDeltaPack
    (remaining accumulator delta dimension bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair delta (pair dimension bound)))

/-- Extracts the unprocessed rows from a matrix-addition state. -/
def machineMatrixAddDeltaRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the reversed accumulated output rows from a matrix-addition state. -/
def machineMatrixAddDeltaAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the fixed rational increment from the matrix-addition state. -/
def machineMatrixAddDeltaDelta (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the binary matrix dimension from the matrix-addition state. -/
def machineMatrixAddDeltaDimension (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Extracts the stored width bound from the matrix-addition state. -/
def machineMatrixAddDeltaBound (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Reads the first unprocessed row of the matrix. -/
def machineMatrixAddDeltaCurrentRow (state : List Bool) : List Bool :=
  machineListHead (machineMatrixAddDeltaRemaining state)

/-- Adds the fixed rational increment to each entry of the current row. -/
def machineMatrixAddDeltaOutputRow (state : List Bool) : List Bool :=
  machineRationalRowAdd
    (pair (machineMatrixAddDeltaDelta state)
      (machineMatrixAddDeltaCurrentRow state))

/-- Prepends the incremented row to the reversed output accumulator. -/
def machineMatrixAddDeltaCandidate (state : List Bool) : List Bool :=
  pair (machineMatrixAddDeltaOutputRow state)
    (machineMatrixAddDeltaAccumulator state)

/-- Truncates the candidate row accumulator to the stored width bound. -/
def machineMatrixAddDeltaNextAccumulator (state : List Bool) : List Bool :=
  (machineMatrixAddDeltaCandidate state).take
    (machineMatrixAddDeltaBound state).length

/-- Consumes one row and stores its incremented output, preserving the increment, dimension, and
bound. -/
def machineMatrixAddDeltaAdvance (state : List Bool) : List Bool :=
  machineMatrixAddDeltaPack
    (machineListTail (machineMatrixAddDeltaRemaining state))
    (machineMatrixAddDeltaNextAccumulator state)
    (machineMatrixAddDeltaDelta state)
    (machineMatrixAddDeltaDimension state)
    (machineMatrixAddDeltaBound state)

/-- Processes the next matrix row, leaving exhausted matrix-addition states fixed. -/
def machineMatrixAddDeltaStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixAddDeltaRemaining state) state
    (machineMatrixAddDeltaAdvance state)

/-- Initializes matrix addition with the source rows, empty output, increment, dimension, and
input bound. -/
def machineMatrixAddDeltaInit (word : List Bool) : List Bool :=
  machineMatrixAddDeltaPack
    (machineMatrixRowsWord (machineMatrixAddDeltaInputMatrix word)) []
    (machineMatrixAddDeltaInputDelta word)
    (machineMatrixDimensionWord (machineMatrixAddDeltaInputMatrix word))
    (machineMatrixAddDeltaInputBound word)

/-- Builds an encoded width envelope for the five components of a matrix-addition state. -/
def machineMatrixAddDeltaWidth (word : List Bool) : List Bool :=
  machineMatrixAddDeltaPack word (machineMatrixAddDeltaInputBound word)
    (machineMatrixAddDeltaInputDelta word) word
    (machineMatrixAddDeltaInputBound word)

/-- Runs matrix addition for one step per input bit. -/
def machineMatrixAddDeltaFinalState (word : List Bool) : List Bool :=
  (machineMatrixAddDeltaStep)^[word.length]
    (machineMatrixAddDeltaInit word)

/-- Pairs the matrix dimension with the accumulated output rows restored to their original
order. -/
def machineMatrixAddDeltaEntries (word : List Bool) : List Bool :=
  let state := machineMatrixAddDeltaFinalState word
  pair (machineMatrixAddDeltaDimension state)
    (machineListReverse (machineMatrixAddDeltaAccumulator state))

theorem machineMatrixAddDeltaPadTwenty_mem_FP :
    machineMatrixAddDeltaPadTwenty ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowAddPadSixteen_mem_FP
    machineRationalRowAddPadFour_mem_FP

theorem machineMatrixAddDeltaPadTwenty_length (word : List Bool) :
    (machineMatrixAddDeltaPadTwenty word).length = 20 * word.length := by
  simp only [machineMatrixAddDeltaPadTwenty, List.length_append,
    machineRationalRowAddPadSixteen_length,
    machineRationalRowAddPadFour,
    machineRationalRowAddPadTwo, List.length_append]
  omega

theorem machineMatrixAddDeltaInputBound_mem_FP :
    machineMatrixAddDeltaInputBound ∈ Complexity.FP := by
  simpa only [machineMatrixAddDeltaInputBound] using!
    machineCompose_mem_FP machineMatrixAddDeltaPadTwenty_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineMatrixAddDeltaInputDelta_mem_FP :
    machineMatrixAddDeltaInputDelta ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineMatrixAddDeltaInputMatrix_mem_FP :
    machineMatrixAddDeltaInputMatrix ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineMatrixAddDeltaInputRows_mem_FP :
    (fun word ↦ machineMatrixRowsWord
      (machineMatrixAddDeltaInputMatrix word)) ∈ Complexity.FP := by
  exact machineCompose_mem_FP machineMatrixAddDeltaInputMatrix_mem_FP
    machineMatrixRowsWord_mem_FP

theorem machineMatrixAddDeltaInputDimension_mem_FP :
    (fun word ↦ machineMatrixDimensionWord
      (machineMatrixAddDeltaInputMatrix word)) ∈ Complexity.FP := by
  exact machineCompose_mem_FP machineMatrixAddDeltaInputMatrix_mem_FP
    machineMatrixDimensionWord_mem_FP

theorem machineMatrixAddDeltaRemaining_mem_FP :
    machineMatrixAddDeltaRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineMatrixAddDeltaAccumulator_mem_FP :
    machineMatrixAddDeltaAccumulator ∈ Complexity.FP := by
  simpa only [machineMatrixAddDeltaAccumulator] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatrixAddDeltaDelta_mem_FP :
    machineMatrixAddDeltaDelta ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineMatrixAddDeltaDelta] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineMatrixAddDeltaDimension_mem_FP :
    machineMatrixAddDeltaDimension ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineMatrixAddDeltaDimension] using!
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineMatrixAddDeltaBound_mem_FP :
    machineMatrixAddDeltaBound ∈ Complexity.FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineMatrixAddDeltaBound] using!
    machineCompose_mem_FP htailThree machinePairSecond_mem_FP

theorem machineMatrixAddDeltaCurrentRow_mem_FP :
    machineMatrixAddDeltaCurrentRow ∈ Complexity.FP := by
  simpa only [machineMatrixAddDeltaCurrentRow] using!
    machineCompose_mem_FP machineMatrixAddDeltaRemaining_mem_FP
      machineListHead_mem_FP

theorem machineMatrixAddDeltaOutputRow_mem_FP :
    machineMatrixAddDeltaOutputRow ∈ Complexity.FP := by
  have hinput := machinePair_mem_FP machineMatrixAddDeltaDelta_mem_FP
    machineMatrixAddDeltaCurrentRow_mem_FP
  simpa only [machineMatrixAddDeltaOutputRow] using!
    machineCompose_mem_FP hinput machineRationalRowAdd_mem_FP

theorem machineMatrixAddDeltaCandidate_mem_FP :
    machineMatrixAddDeltaCandidate ∈ Complexity.FP :=
  machinePair_mem_FP machineMatrixAddDeltaOutputRow_mem_FP
    machineMatrixAddDeltaAccumulator_mem_FP

theorem machineMatrixAddDeltaNextAccumulator_mem_FP :
    machineMatrixAddDeltaNextAccumulator ∈ Complexity.FP := by
  simpa only [machineMatrixAddDeltaNextAccumulator] using!
    machineTake_mem_FP machineMatrixAddDeltaBound_mem_FP
      machineMatrixAddDeltaCandidate_mem_FP

theorem machineMatrixAddDeltaAdvance_mem_FP :
    machineMatrixAddDeltaAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineMatrixAddDeltaRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineMatrixAddDeltaNextAccumulator_mem_FP
      (machinePair_mem_FP machineMatrixAddDeltaDelta_mem_FP
        (machinePair_mem_FP machineMatrixAddDeltaDimension_mem_FP
          machineMatrixAddDeltaBound_mem_FP)))

theorem machineMatrixAddDeltaStep_mem_FP :
    machineMatrixAddDeltaStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineMatrixAddDeltaRemaining_mem_FP
    id_mem_FP machineMatrixAddDeltaAdvance_mem_FP

theorem machineMatrixAddDeltaInit_mem_FP :
    machineMatrixAddDeltaInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixAddDeltaInputRows_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineMatrixAddDeltaInputDelta_mem_FP
        (machinePair_mem_FP machineMatrixAddDeltaInputDimension_mem_FP
          machineMatrixAddDeltaInputBound_mem_FP)))

theorem machineMatrixAddDeltaWidth_mem_FP :
    machineMatrixAddDeltaWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineMatrixAddDeltaInputBound_mem_FP
      (machinePair_mem_FP machineMatrixAddDeltaInputDelta_mem_FP
        (machinePair_mem_FP id_mem_FP
          machineMatrixAddDeltaInputBound_mem_FP)))

@[simp] theorem machineMatrixAddDeltaRemaining_pack (a b c d e) :
    machineMatrixAddDeltaRemaining
      (machineMatrixAddDeltaPack a b c d e) = a := by
  simp [machineMatrixAddDeltaRemaining, machineMatrixAddDeltaPack]

@[simp] theorem machineMatrixAddDeltaAccumulator_pack (a b c d e) :
    machineMatrixAddDeltaAccumulator
      (machineMatrixAddDeltaPack a b c d e) = b := by
  simp [machineMatrixAddDeltaAccumulator, machineMatrixAddDeltaPack]

@[simp] theorem machineMatrixAddDeltaDelta_pack (a b c d e) :
    machineMatrixAddDeltaDelta
      (machineMatrixAddDeltaPack a b c d e) = c := by
  simp [machineMatrixAddDeltaDelta, machineMatrixAddDeltaPack]

@[simp] theorem machineMatrixAddDeltaDimension_pack (a b c d e) :
    machineMatrixAddDeltaDimension
      (machineMatrixAddDeltaPack a b c d e) = d := by
  simp [machineMatrixAddDeltaDimension, machineMatrixAddDeltaPack]

@[simp] theorem machineMatrixAddDeltaBound_pack (a b c d e) :
    machineMatrixAddDeltaBound
      (machineMatrixAddDeltaPack a b c d e) = e := by
  simp [machineMatrixAddDeltaBound, machineMatrixAddDeltaPack]

/-- Bounds matrix-addition state lengths and preserves the input increment and width bound. -/
def MachineMatrixAddDeltaStateBound (word state : List Bool) : Prop :=
  state = machineMatrixAddDeltaPack
      (machineMatrixAddDeltaRemaining state)
      (machineMatrixAddDeltaAccumulator state)
      (machineMatrixAddDeltaDelta state)
      (machineMatrixAddDeltaDimension state)
      (machineMatrixAddDeltaBound state) ∧
    (machineMatrixAddDeltaRemaining state).length ≤ word.length ∧
    (machineMatrixAddDeltaAccumulator state).length ≤
      (machineMatrixAddDeltaInputBound word).length ∧
    machineMatrixAddDeltaDelta state =
      machineMatrixAddDeltaInputDelta word ∧
    (machineMatrixAddDeltaDimension state).length ≤ word.length ∧
    machineMatrixAddDeltaBound state = machineMatrixAddDeltaInputBound word

theorem machineMatrixAddDeltaInit_bound (word : List Bool) :
    MachineMatrixAddDeltaStateBound word (machineMatrixAddDeltaInit word) := by
  simp only [MachineMatrixAddDeltaStateBound, machineMatrixAddDeltaInit,
    machineMatrixAddDeltaRemaining_pack,
    machineMatrixAddDeltaAccumulator_pack,
    machineMatrixAddDeltaDelta_pack,
    machineMatrixAddDeltaDimension_pack,
    machineMatrixAddDeltaBound_pack]
  refine ⟨trivial, ?_, by simp, trivial, ?_, trivial⟩
  · exact (machinePairSecond_length_le
      (machineMatrixAddDeltaInputMatrix word)).trans
        (machinePairSecond_length_le word)
  · exact (machinePairFirst_length_le
      (machineMatrixAddDeltaInputMatrix word)).trans
        (machinePairSecond_length_le word)

theorem machineMatrixAddDeltaStep_bound {word state : List Bool}
    (hstate : MachineMatrixAddDeltaStateBound word state) :
    MachineMatrixAddDeltaStateBound word
      (machineMatrixAddDeltaStep state) := by
  rcases hstate with
    ⟨hdecomp, hremaining, haccumulator, hdelta, hdimension, hbound⟩
  by_cases hnil : machineMatrixAddDeltaRemaining state = []
  · rw [machineMatrixAddDeltaStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, haccumulator, hdelta, hdimension, hbound⟩
  · rw [machineMatrixAddDeltaStep]
    cases hremainingCode : machineMatrixAddDeltaRemaining state with
    | nil => exact False.elim (hnil hremainingCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixAddDeltaAdvance]
        simp only [MachineMatrixAddDeltaStateBound,
          machineMatrixAddDeltaRemaining_pack,
          machineMatrixAddDeltaAccumulator_pack,
          machineMatrixAddDeltaDelta_pack,
          machineMatrixAddDeltaDimension_pack,
          machineMatrixAddDeltaBound_pack]
        refine ⟨trivial, ?_, ?_, hdelta, hdimension, hbound⟩
        · exact (machineListTail_length_le
            (machineMatrixAddDeltaRemaining state)).trans hremaining
        · rw [machineMatrixAddDeltaNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineMatrixAddDeltaIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixAddDeltaStateBound word
      ((machineMatrixAddDeltaStep)^[k]
        (machineMatrixAddDeltaInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixAddDeltaInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixAddDeltaStep_bound ih

theorem machineMatrixAddDeltaIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineMatrixAddDeltaStep)^[iterations]
      (machineMatrixAddDeltaInit word)).length ≤
        (machineMatrixAddDeltaWidth word).length := by
  rcases machineMatrixAddDeltaIterate_bound word iterations with
    ⟨hdecomp, hremaining, haccumulator, hdelta, hdimension, hbound⟩
  rw [hdecomp, hdelta, hbound]
  simp only [machineMatrixAddDeltaPack, machineMatrixAddDeltaWidth,
    pair_length]
  omega

theorem machineMatrixAddDeltaFinalState_mem_FP :
    machineMatrixAddDeltaFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixAddDeltaStep_mem_FP
    machineMatrixAddDeltaInit_mem_FP id_mem_FP
    machineMatrixAddDeltaWidth_mem_FP
    machineMatrixAddDeltaIterate_length_le_width

theorem machineMatrixAddDeltaEntries_mem_FP :
    machineMatrixAddDeltaEntries ∈ Complexity.FP := by
  have hdimension := machineCompose_mem_FP
    machineMatrixAddDeltaFinalState_mem_FP
    machineMatrixAddDeltaDimension_mem_FP
  have hacc := machineCompose_mem_FP
    machineMatrixAddDeltaFinalState_mem_FP
    machineMatrixAddDeltaAccumulator_mem_FP
  have hrows := machineCompose_mem_FP hacc machineListReverse_mem_FP
  simpa only [machineMatrixAddDeltaEntries] using!
    machinePair_mem_FP hdimension hrows

/-! ## Output-size bound on canonical matrices -/

private theorem matrixAddDelta_natList_sum_le_length_mul
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

private theorem matrixAddDelta_outputCode_length_le
    (delta : RawRat) (budget : ℕ) : ∀ rows : List (List ℚ),
    (∀ row ∈ rows, ∀ q ∈ row,
      (rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat q).add delta))).length ≤
          172 + 72 * budget) →
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rows.map (rationalRowAddValues delta))).length ≤
      (rows.map List.length).sum * (692 + 288 * budget) +
        2 * rows.length := by
  intro rows hentry
  induction rows with
  | nil => simp [binaryListCode]
  | cons row rows ih =>
      have hrowEntry : ∀ q ∈ row,
          (rationalEntryBinaryCode
            (binaryNormalizeRawRat ((rawRatOfRat q).add delta))).length ≤
              172 + 72 * budget := by
        intro q hq
        exact hentry row (by simp) q hq
      have htailEntry : ∀ tailRow ∈ rows, ∀ q ∈ tailRow,
          (rationalEntryBinaryCode
            (binaryNormalizeRawRat ((rawRatOfRat q).add delta))).length ≤
              172 + 72 * budget := by
        intro tailRow htailRow q hq
        exact hentry tailRow (by simp [htailRow]) q hq
      have hinner :
          (binaryListCode rationalEntryBinaryCode
            (rationalRowAddValues delta row)).length ≤
              row.length * (346 + 144 * budget) := by
        rw [binaryListCode_length_eq_sum]
        have hterm : ∀ value ∈
            ((rationalRowAddValues delta row).map
              fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2),
            value ≤ 346 + 144 * budget := by
          simp only [rationalRowAddValues, List.map_map]
          intro value hvalue
          rw [List.mem_map] at hvalue
          rcases hvalue with ⟨q, hq, rfl⟩
          have hqBound := hrowEntry q hq
          simp only [Function.comp_apply]
          omega
        have hsum := matrixAddDelta_natList_sum_le_length_mul hterm
        simpa only [rationalRowAddValues, List.length_map] using! hsum
      have htail := ih htailEntry
      simp only [List.map_cons, binaryListCode, pair_length,
        List.map_map, List.sum_cons, List.length_cons] at htail ⊢
      nlinarith

theorem machineMatrixAddDelta_outputRows_length_le_bound {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) :
    let matrixWord := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
    let word := pair (rawRatBinaryCode delta) matrixWord
    let output := (rationalMatrixRows A).map
      (rationalRowAddValues delta)
    (binaryListCode (binaryListCode rationalEntryBinaryCode) output).length ≤
      (machineMatrixAddDeltaInputBound word).length := by
  dsimp only
  let matrixWord := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let word := pair (rawRatBinaryCode delta) matrixWord
  let rows := rationalMatrixRows A
  have hrowsMatrixCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        matrixWord.length := by
    calc
      _ = (machineMatrixRowsWord matrixWord).length := by
        simpa only [matrixWord, rows] using! congrArg List.length
          (machineMatrixRowsWord_encode A).symm
      _ ≤ matrixWord.length := by
        simpa only [machineMatrixRowsWord] using!
          machinePairSecond_length_le matrixWord
  have hmatrixWord : matrixWord.length ≤ word.length := by
    simpa only [word, machinePairSecond_pair] using!
      machinePairSecond_length_le word
  have hrowsCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := hrowsMatrixCode.trans hmatrixWord
  have hdeltaWidth : rawRatWidth delta ≤ word.length := by
    have hdeltaCode : (rawRatBinaryCode delta).length ≤ word.length := by
      simpa only [word, machinePairFirst_pair] using!
        machinePairFirst_length_le word
    exact (rawRatWidth_le_binaryCode_length delta).trans hdeltaCode
  have hentry : ∀ row ∈ rows, ∀ q ∈ row,
      (rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat q).add delta))).length ≤
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
    have hadd := rawRatWidth_add_le (rawRatOfRat q) delta
    have hnormalize :=
      rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
        ((rawRatOfRat q).add delta)
    omega
  have houtput := matrixAddDelta_outputCode_length_le
    delta word.length rows hentry
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsCode
  rw [matrixNonnegativeRowsWork_eq_length_add_entries] at hwork
  have hquadratic :
      (rows.map List.length).sum * (692 + 288 * word.length) +
          2 * rows.length ≤
        (machineMatrixAddDeltaInputBound word).length := by
    rw [machineMatrixAddDeltaInputBound]
    simp only [machineBinaryMulWidth, List.length_replicate,
      List.length_append]
    rw [machineMatrixAddDeltaPadTwenty_length]
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

/-- Adds the raw-rational increment to every entry of every supplied row. -/
def rationalMatrixAddRows (delta : RawRat)
    (rows : List (List ℚ)) : List (List ℚ) :=
  rows.map (rationalRowAddValues delta)

/-- Encodes a square rational matrix together with the raw-rational increment to add. -/
def machineMatrixAddDeltaCanonicalInput {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  pair (rawRatBinaryCode delta)
    (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)

/-- Encodes matrix addition after `k` rows, with untouched remaining rows and reversed processed
output. -/
def machineMatrixAddDeltaSemanticState
    (word dimension : List Bool) (delta : RawRat)
    (rows : List (List ℚ)) (k : ℕ) : List Bool :=
  let output := rationalMatrixAddRows delta rows
  machineMatrixAddDeltaPack
    (binaryListCode (binaryListCode rationalEntryBinaryCode) (rows.drop k))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (output.take k).reverse)
    (rawRatBinaryCode delta) dimension
    (machineMatrixAddDeltaInputBound word)

theorem machineMatrixAddDeltaInit_encode {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) :
    let word := machineMatrixAddDeltaCanonicalInput delta A
    machineMatrixAddDeltaInit word =
      machineMatrixAddDeltaSemanticState word n.bits delta
        (rationalMatrixRows A) 0 := by
  dsimp only
  simp only [machineMatrixAddDeltaInit,
    machineMatrixAddDeltaCanonicalInput,
    machineMatrixAddDeltaInputMatrix, machinePairSecond_pair,
    machineMatrixAddDeltaInputDelta, machinePairFirst_pair,
    machineMatrixRowsWord_encode,
    machineMatrixDimensionWord_encode,
    machineMatrixAddDeltaSemanticState, List.drop_zero,
    List.take_zero, List.reverse_nil, binaryListCode]

theorem machineMatrixAddDeltaOutputRow_semantics
    (word dimension : List Bool) (delta : RawRat)
    (rows : List (List ℚ)) (k : ℕ) (hk : k < rows.length) :
    machineMatrixAddDeltaOutputRow
        (machineMatrixAddDeltaSemanticState word dimension delta rows k) =
      binaryListCode rationalEntryBinaryCode
        (rationalRowAddValues delta rows[k]) := by
  have hdrop := List.drop_eq_getElem_cons hk
  rw [machineMatrixAddDeltaOutputRow]
  simp only [machineMatrixAddDeltaSemanticState,
    machineMatrixAddDeltaDelta_pack,
    machineMatrixAddDeltaCurrentRow,
    machineMatrixAddDeltaRemaining_pack, hdrop,
    machineListHead_cons]
  change machineRationalRowAdd
      (machineRationalRowAddCanonicalInput delta rows[k]) = _
  exact machineRationalRowAdd_encode delta rows[k]

theorem machineMatrixAddDeltaStep_semantics
    (word dimension : List Bool) (delta : RawRat)
    (rows : List (List ℚ)) (k : ℕ) (hk : k < rows.length)
    (hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixAddRows delta rows)).length ≤
          (machineMatrixAddDeltaInputBound word).length) :
    machineMatrixAddDeltaStep
        (machineMatrixAddDeltaSemanticState word dimension delta rows k) =
      machineMatrixAddDeltaSemanticState word dimension delta rows (k + 1) := by
  let output := rationalMatrixAddRows delta rows
  have houtputLength : output.length = rows.length := by
    simp [output, rationalMatrixAddRows]
  have hkoutput : k < output.length := by omega
  have houtputGet : output[k] =
      rationalRowAddValues delta rows[k] := by
    simp [output, rationalMatrixAddRows, List.getElem_map]
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
          (machineMatrixAddDeltaInputBound word).length :=
    (binaryListCode_take_reverse_length_le
      (binaryListCode rationalEntryBinaryCode) output (k + 1)).trans
        (by simpa only [output] using! hfullBound)
  have htakeBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (output.take (k + 1)).reverse).take
            (machineMatrixAddDeltaInputBound word).length =
        binaryListCode (binaryListCode rationalEntryBinaryCode)
          (output.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hnonempty :
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rows.drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil _ _ _
  rw [machineMatrixAddDeltaStep]
  simp only [machineMatrixAddDeltaSemanticState,
    machineMatrixAddDeltaRemaining_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hnonempty,
    machineMatrixAddDeltaAdvance]
  simp only [machineMatrixAddDeltaRemaining_pack,
    machineMatrixAddDeltaAccumulator_pack,
    machineMatrixAddDeltaDelta_pack,
    machineMatrixAddDeltaDimension_pack,
    machineMatrixAddDeltaBound_pack,
    machineMatrixAddDeltaNextAccumulator,
    machineMatrixAddDeltaCandidate]
  have hrow :
      machineMatrixAddDeltaOutputRow
          (machineMatrixAddDeltaPack
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              (rows.drop k))
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              (output.take k).reverse)
            (rawRatBinaryCode delta) dimension
            (machineMatrixAddDeltaInputBound word)) =
        binaryListCode rationalEntryBinaryCode output[k] := by
    rw [houtputGet]
    simpa only [machineMatrixAddDeltaSemanticState, output] using!
      machineMatrixAddDeltaOutputRow_semantics
        word dimension delta rows k hk
  rw [hrow, hdrop, machineListTail_cons]
  change machineMatrixAddDeltaPack
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rows.drop (k + 1)))
      ((binaryListCode (binaryListCode rationalEntryBinaryCode)
        (output[k] :: (output.take k).reverse)).take
          (machineMatrixAddDeltaInputBound word).length)
      (rawRatBinaryCode delta) dimension
      (machineMatrixAddDeltaInputBound word) = _
  rw [← hprefix, htakeBound]

theorem machineMatrixAddDeltaIterate_semantics
    (word dimension : List Bool) (delta : RawRat)
    (rows : List (List ℚ))
    (hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixAddRows delta rows)).length ≤
          (machineMatrixAddDeltaInputBound word).length) : ∀ k ≤ rows.length,
    (machineMatrixAddDeltaStep)^[k]
        (machineMatrixAddDeltaSemanticState word dimension delta rows 0) =
      machineMatrixAddDeltaSemanticState word dimension delta rows k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineMatrixAddDeltaStep_semantics word dimension delta rows k
        (by omega) hfullBound

theorem machineMatrixAddDelta_done_iterate
    (extra : ℕ) (accumulator delta dimension bound : List Bool) :
    (machineMatrixAddDeltaStep)^[extra]
        (machineMatrixAddDeltaPack [] accumulator delta dimension bound) =
      machineMatrixAddDeltaPack [] accumulator delta dimension bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineMatrixAddDeltaStep]

theorem machineMatrixAddDeltaFinalState_encode {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) :
    let word := machineMatrixAddDeltaCanonicalInput delta A
    let rows := rationalMatrixRows A
    machineMatrixAddDeltaFinalState word =
      machineMatrixAddDeltaPack []
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixAddRows delta rows).reverse)
        (rawRatBinaryCode delta) n.bits
        (machineMatrixAddDeltaInputBound word) := by
  dsimp only
  let word := machineMatrixAddDeltaCanonicalInput delta A
  let matrixWord := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let rows := rationalMatrixRows A
  have hrowsLength : rows.length ≤ word.length := by
    have hn : rows.length ≤ matrixWord.length := by
      simpa only [rows, matrixWord, rationalMatrixRows, List.length_ofFn] using!
        matrix_dimension_le_code_length A
    have hm : matrixWord.length ≤ word.length := by
      simpa only [word, machineMatrixAddDeltaCanonicalInput,
        machinePairSecond_pair] using! machinePairSecond_length_le word
    exact hn.trans hm
  have hfullBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixAddRows delta rows)).length ≤
          (machineMatrixAddDeltaInputBound word).length := by
    simpa only [word, rows, machineMatrixAddDeltaCanonicalInput,
      rationalMatrixAddRows] using!
      machineMatrixAddDelta_outputRows_length_le_bound delta A
  have hsplit : word.length =
      (word.length - rows.length) + rows.length := by omega
  have htakeAll :
      (rationalMatrixAddRows delta rows).take rows.length =
        rationalMatrixAddRows delta rows := by
    have hlength : (rationalMatrixAddRows delta rows).length =
        rows.length := by simp [rationalMatrixAddRows]
    rw [← hlength, List.take_length]
  change (machineMatrixAddDeltaStep)^[word.length]
      (machineMatrixAddDeltaInit word) = _
  rw [hsplit, Function.iterate_add_apply,
    machineMatrixAddDeltaInit_encode delta A,
    machineMatrixAddDeltaIterate_semantics word n.bits delta rows
      hfullBound rows.length le_rfl]
  simp only [machineMatrixAddDeltaSemanticState, List.drop_length,
    binaryListCode]
  rw [htakeAll, machineMatrixAddDelta_done_iterate]

/-- Adds `delta.value` to every entry of a square rational matrix. -/
def rationalMatrixAddDeltaSemantic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (delta : RawRat) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ A i j + delta.value

theorem rationalMatrixAddRows_semantics {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixAddRows delta (rationalMatrixRows A) =
      rationalMatrixRows (rationalMatrixAddDeltaSemantic A delta) := by
  apply List.ext_get
  · simp [rationalMatrixAddRows, rationalMatrixRows]
  · intro i hi hi'
    apply List.ext_get
    · simp [rationalMatrixAddRows, rationalRowAddValues,
        rationalMatrixRows]
    · intro j hj hj'
      simp [rationalMatrixAddRows, rationalRowAddValues,
        rationalMatrixRows, rationalMatrixAddDeltaSemantic,
        binaryNormalizeRawRat_eq_value, RawRat.value_add,
        rawRatOfRat_value]

@[simp] theorem machineMatrixAddDeltaEntries_encode {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixAddDeltaEntries
        (machineMatrixAddDeltaCanonicalInput delta A) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, rationalMatrixAddDeltaSemantic A delta⟩ := by
  let rows := rationalMatrixRows A
  rw [machineMatrixAddDeltaEntries,
    machineMatrixAddDeltaFinalState_encode delta A]
  simp only [machineMatrixAddDeltaDimension_pack,
    machineMatrixAddDeltaAccumulator_pack,
    machineListReverse_encode, List.reverse_reverse]
  rw [rationalMatrixAddRows_semantics delta A]
  rfl

@[simp] theorem machineMatrixAddDeltaEntries_rational {n : ℕ}
    (delta : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixAddDeltaEntries
        (pair (rawRatBinaryCode (rawRatOfRat delta))
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalMatrixBinaryEncoding.encode
        ⟨n, fun i j ↦ A i j + delta⟩ := by
  rw [show pair (rawRatBinaryCode (rawRatOfRat delta))
      (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
        machineMatrixAddDeltaCanonicalInput (rawRatOfRat delta) A from rfl,
    machineMatrixAddDeltaEntries_encode]
  congr 2
  funext i j
  simp [rationalMatrixAddDeltaSemantic]

end BeyondBethe
