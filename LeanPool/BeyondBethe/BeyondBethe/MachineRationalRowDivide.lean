/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse
public import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalUnary
public import Mathlib.Tactic

/-!
# Dividing every entry of a rational row by one raw rational

The input is `pair scaleRawCode rowCode`.  Each output entry is normalized to
the numerator/denominator pair encoding required inside rational matrices.
This is deliberately not `machineRationalDivCode`, whose public output uses a
different one-natural encoding.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the fixed raw divisor from a row-division request. -/
def machineRationalRowDivideScale (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the encoded rational row from a row-division request. -/
def machineRationalRowDivideRow (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Concatenates two copies of a word for row-division width padding. -/
def machineRationalRowDividePadTwo (word : List Bool) : List Bool :=
  word ++ word

/-- Concatenates four copies of a word for row-division width padding. -/
def machineRationalRowDividePadFour (word : List Bool) : List Bool :=
  machineRationalRowDividePadTwo word ++ machineRationalRowDividePadTwo word

/-- Concatenates eight copies of a word for row-division width padding. -/
def machineRationalRowDividePadEight (word : List Bool) : List Bool :=
  machineRationalRowDividePadFour word ++ machineRationalRowDividePadFour word

/-- Concatenates sixteen copies of a word for row-division width padding. -/
def machineRationalRowDividePadSixteen (word : List Bool) : List Bool :=
  machineRationalRowDividePadEight word ++ machineRationalRowDividePadEight word

/-- A coefficient-adjusted quadratic envelope.  Sixteen copies before the
standard square provide enough room for every normalized output entry without
the impractical quartic padding used by an earlier draft. -/
def machineRationalRowDivideInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineRationalRowDividePadSixteen word)

/-- Packs the unprocessed row, reversed output accumulator, fixed divisor, and bound for row
division. -/
def machineRationalRowDividePack
    (remaining accumulator scale bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair scale bound))

/-- Extracts the unprocessed encoded row from a row-division state. -/
def machineRationalRowDivideRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the reverse-order output accumulator from a row-division state. -/
def machineRationalRowDivideAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the fixed raw divisor from a row-division state. -/
def machineRationalRowDivideScaleField (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the accumulator length-bound word from a row-division state. -/
def machineRationalRowDivideBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

/-- Divides the next row entry by the fixed scale in raw rational arithmetic. -/
def machineRationalRowDivideRawEntry (state : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineListHead (machineRationalRowDivideRemaining state))
      (machineRationalRowDivideScaleField state))

/-- Normalizes the divided row entry into its rational entry encoding. -/
def machineRationalRowDivideEntry (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRationalRowDivideRawEntry state)

/-- Prepends the normalized divided entry to the reverse-order output accumulator. -/
def machineRationalRowDivideCandidate (state : List Bool) : List Bool :=
  pair (machineRationalRowDivideEntry state)
    (machineRationalRowDivideAccumulator state)

/-- Truncates the candidate row-division accumulator to the stored bound length. -/
def machineRationalRowDivideNextAccumulator (state : List Bool) : List Bool :=
  (machineRationalRowDivideCandidate state).take
    (machineRationalRowDivideBound state).length

/-- Consumes the next row entry and stores the bounded updated accumulator, preserving divisor
and bound. -/
def machineRationalRowDivideAdvance (state : List Bool) : List Bool :=
  machineRationalRowDividePack
    (machineListTail (machineRationalRowDivideRemaining state))
    (machineRationalRowDivideNextAccumulator state)
    (machineRationalRowDivideScaleField state)
    (machineRationalRowDivideBound state)

/-- Fixes an exhausted row-division state and otherwise processes one entry. -/
def machineRationalRowDivideStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalRowDivideRemaining state) state
    (machineRationalRowDivideAdvance state)

/-- Initializes row division with the requested row, empty accumulator, fixed divisor, and
computed bound. -/
def machineRationalRowDivideInit (word : List Bool) : List Bool :=
  machineRationalRowDividePack (machineRationalRowDivideRow word) []
    (machineRationalRowDivideScale word)
    (machineRationalRowDivideInputBound word)

/-- Packs input and bound words in the four-field layout to bound the row-division state. -/
def machineRationalRowDivideWidth (word : List Bool) : List Bool :=
  let bound := machineRationalRowDivideInputBound word
  machineRationalRowDividePack word bound word bound

/-- Runs the row-division scan once per input bit from its initial state. -/
def machineRationalRowDivideFinalState (word : List Bool) : List Bool :=
  (machineRationalRowDivideStep)^[word.length]
    (machineRationalRowDivideInit word)

/-- Reverses the final accumulator to return the divided rational row in its original order. -/
def machineRationalRowDivide (word : List Bool) : List Bool :=
  machineListReverse
    (machineRationalRowDivideAccumulator
      (machineRationalRowDivideFinalState word))

theorem machineRationalRowDivideScale_mem_FP :
    machineRationalRowDivideScale ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRationalRowDivideRow_mem_FP :
    machineRationalRowDivideRow ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineRationalRowDividePadTwo_mem_FP :
    machineRationalRowDividePadTwo ∈ Complexity.FP :=
  machineAppend_mem_FP id_mem_FP id_mem_FP

theorem machineRationalRowDividePadFour_mem_FP :
    machineRationalRowDividePadFour ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowDividePadTwo_mem_FP
    machineRationalRowDividePadTwo_mem_FP

theorem machineRationalRowDividePadEight_mem_FP :
    machineRationalRowDividePadEight ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowDividePadFour_mem_FP
    machineRationalRowDividePadFour_mem_FP

theorem machineRationalRowDividePadSixteen_mem_FP :
    machineRationalRowDividePadSixteen ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowDividePadEight_mem_FP
    machineRationalRowDividePadEight_mem_FP

theorem machineRationalRowDivideInputBound_mem_FP :
    machineRationalRowDivideInputBound ∈ Complexity.FP := by
  simpa only [machineRationalRowDivideInputBound] using!
    machineCompose_mem_FP machineRationalRowDividePadSixteen_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineRationalRowDividePadSixteen_length (word : List Bool) :
    (machineRationalRowDividePadSixteen word).length = 16 * word.length := by
  simp only [machineRationalRowDividePadSixteen,
    machineRationalRowDividePadEight,
    machineRationalRowDividePadFour,
    machineRationalRowDividePadTwo, List.length_append]
  omega

theorem machineRationalRowDivideInputBound_length_mono
    {left right : List Bool} (h : left.length ≤ right.length) :
    (machineRationalRowDivideInputBound left).length ≤
      (machineRationalRowDivideInputBound right).length := by
  apply machineBinaryMulWidth_length_mono
  rw [machineRationalRowDividePadSixteen_length,
    machineRationalRowDividePadSixteen_length]
  exact Nat.mul_le_mul_left 16 h

theorem machineRationalRowDivideRemaining_mem_FP :
    machineRationalRowDivideRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRationalRowDivideAccumulator_mem_FP :
    machineRationalRowDivideAccumulator ∈ Complexity.FP := by
  simpa only [machineRationalRowDivideAccumulator] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalRowDivideScaleField_mem_FP :
    machineRationalRowDivideScaleField ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineRationalRowDivideScaleField] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineRationalRowDivideBound_mem_FP :
    machineRationalRowDivideBound ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineRationalRowDivideBound] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineRationalRowDivideRawEntry_mem_FP :
    machineRationalRowDivideRawEntry ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP machineRationalRowDivideRemaining_mem_FP
    machineListHead_mem_FP
  have hinput := machinePair_mem_FP hhead
    machineRationalRowDivideScaleField_mem_FP
  simpa only [machineRationalRowDivideRawEntry] using!
    machineCompose_mem_FP hinput machineRawRatDivCode_mem_FP

theorem machineRationalRowDivideEntry_mem_FP :
    machineRationalRowDivideEntry ∈ Complexity.FP := by
  simpa only [machineRationalRowDivideEntry] using!
    machineCompose_mem_FP machineRationalRowDivideRawEntry_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineRationalRowDivideCandidate_mem_FP :
    machineRationalRowDivideCandidate ∈ Complexity.FP :=
  machinePair_mem_FP machineRationalRowDivideEntry_mem_FP
    machineRationalRowDivideAccumulator_mem_FP

theorem machineRationalRowDivideNextAccumulator_mem_FP :
    machineRationalRowDivideNextAccumulator ∈ Complexity.FP := by
  simpa only [machineRationalRowDivideNextAccumulator] using!
    machineTake_mem_FP machineRationalRowDivideBound_mem_FP
      machineRationalRowDivideCandidate_mem_FP

theorem machineRationalRowDivideAdvance_mem_FP :
    machineRationalRowDivideAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineRationalRowDivideRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalRowDivideNextAccumulator_mem_FP
      (machinePair_mem_FP machineRationalRowDivideScaleField_mem_FP
        machineRationalRowDivideBound_mem_FP))

theorem machineRationalRowDivideStep_mem_FP :
    machineRationalRowDivideStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineRationalRowDivideRemaining_mem_FP
    id_mem_FP machineRationalRowDivideAdvance_mem_FP

theorem machineRationalRowDivideInit_mem_FP :
    machineRationalRowDivideInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRationalRowDivideRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineRationalRowDivideScale_mem_FP
        machineRationalRowDivideInputBound_mem_FP))

theorem machineRationalRowDivideWidth_mem_FP :
    machineRationalRowDivideWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineRationalRowDivideInputBound_mem_FP
      (machinePair_mem_FP id_mem_FP
        machineRationalRowDivideInputBound_mem_FP))

@[simp] theorem machineRationalRowDivideRemaining_pack (a b c d) :
    machineRationalRowDivideRemaining
      (machineRationalRowDividePack a b c d) = a := by
  simp [machineRationalRowDivideRemaining, machineRationalRowDividePack]

@[simp] theorem machineRationalRowDivideAccumulator_pack (a b c d) :
    machineRationalRowDivideAccumulator
      (machineRationalRowDividePack a b c d) = b := by
  simp [machineRationalRowDivideAccumulator, machineRationalRowDividePack]

@[simp] theorem machineRationalRowDivideScaleField_pack (a b c d) :
    machineRationalRowDivideScaleField
      (machineRationalRowDividePack a b c d) = c := by
  simp [machineRationalRowDivideScaleField, machineRationalRowDividePack]

@[simp] theorem machineRationalRowDivideBound_pack (a b c d) :
    machineRationalRowDivideBound
      (machineRationalRowDividePack a b c d) = d := by
  simp [machineRationalRowDivideBound, machineRationalRowDividePack]

/-- Requires exact row-division state packing, input-bounded remaining row and divisor, a
bounded accumulator, and the prescribed bound word. -/
def MachineRationalRowDivideStateBound (word state : List Bool) : Prop :=
  state = machineRationalRowDividePack
      (machineRationalRowDivideRemaining state)
      (machineRationalRowDivideAccumulator state)
      (machineRationalRowDivideScaleField state)
      (machineRationalRowDivideBound state) ∧
    (machineRationalRowDivideRemaining state).length ≤ word.length ∧
    (machineRationalRowDivideAccumulator state).length ≤
      (machineRationalRowDivideInputBound word).length ∧
    (machineRationalRowDivideScaleField state).length ≤ word.length ∧
    machineRationalRowDivideBound state =
      machineRationalRowDivideInputBound word

theorem machineRationalRowDivideInit_bound (word : List Bool) :
    MachineRationalRowDivideStateBound word
      (machineRationalRowDivideInit word) := by
  simp only [MachineRationalRowDivideStateBound,
    machineRationalRowDivideInit,
    machineRationalRowDivideRemaining_pack,
    machineRationalRowDivideAccumulator_pack,
    machineRationalRowDivideScaleField_pack,
    machineRationalRowDivideBound_pack]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineRationalRowDivideRow] using!
      machinePairSecond_length_le word
  · simpa only [machineRationalRowDivideScale] using!
      machinePairFirst_length_le word

theorem machineRationalRowDivideStep_bound {word state : List Bool}
    (hstate : MachineRationalRowDivideStateBound word state) :
    MachineRationalRowDivideStateBound word
      (machineRationalRowDivideStep state) := by
  rcases hstate with
    ⟨hdecomp, hremaining, haccumulator, hscale, hbound⟩
  by_cases hnil : machineRationalRowDivideRemaining state = []
  · rw [machineRationalRowDivideStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, haccumulator, hscale, hbound⟩
  · rw [machineRationalRowDivideStep]
    cases hremainingCode : machineRationalRowDivideRemaining state with
    | nil => exact False.elim (hnil hremainingCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineRationalRowDivideAdvance]
        simp only [MachineRationalRowDivideStateBound,
          machineRationalRowDivideRemaining_pack,
          machineRationalRowDivideAccumulator_pack,
          machineRationalRowDivideScaleField_pack,
          machineRationalRowDivideBound_pack]
        refine ⟨trivial, ?_, ?_, hscale, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalRowDivideRemaining state)).trans hremaining
        · rw [machineRationalRowDivideNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalRowDivideIterate_bound (word : List Bool) : ∀ k,
    MachineRationalRowDivideStateBound word
      ((machineRationalRowDivideStep)^[k]
        (machineRationalRowDivideInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalRowDivideInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalRowDivideStep_bound ih

theorem machineRationalRowDivideIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineRationalRowDivideStep)^[iterations]
      (machineRationalRowDivideInit word)).length ≤
        (machineRationalRowDivideWidth word).length := by
  rcases machineRationalRowDivideIterate_bound word iterations with
    ⟨hdecomp, hremaining, haccumulator, hscale, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalRowDividePack,
    machineRationalRowDivideWidth, pair_length]
  omega

theorem machineRationalRowDivideFinalState_mem_FP :
    machineRationalRowDivideFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineRationalRowDivideStep_mem_FP
    machineRationalRowDivideInit_mem_FP id_mem_FP
    machineRationalRowDivideWidth_mem_FP
    machineRationalRowDivideIterate_length_le_width

theorem machineRationalRowDivide_mem_FP :
    machineRationalRowDivide ∈ Complexity.FP := by
  have hacc := machineCompose_mem_FP
    machineRationalRowDivideFinalState_mem_FP
    machineRationalRowDivideAccumulator_mem_FP
  simpa only [machineRationalRowDivide] using!
    machineCompose_mem_FP hacc machineListReverse_mem_FP

/-! ## Ordinary output-size estimate -/

private theorem natList_sum_le_length_mul {values : List ℕ} {bound : ℕ}
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

theorem machineRationalRowDivide_output_length_le_bound
    (scale : RawRat) (row : List ℚ) :
    let word := pair (rawRatBinaryCode scale)
      (binaryListCode rationalEntryBinaryCode row)
    let output := row.map fun q ↦
      binaryNormalizeRawRat ((rawRatOfRat q).div scale)
    (binaryListCode rationalEntryBinaryCode output).length ≤
      (machineRationalRowDivideInputBound word).length := by
  dsimp only
  let word := pair (rawRatBinaryCode scale)
    (binaryListCode rationalEntryBinaryCode row)
  have hscale : rawRatWidth scale ≤ word.length := by
    have hcomponent : (rawRatBinaryCode scale).length ≤ word.length := by
      simpa only [word, machinePairFirst_pair] using!
        machinePairFirst_length_le word
    exact (rawRatWidth_le_binaryCode_length scale).trans
      hcomponent
  have hrowLength : row.length ≤ word.length := by
    have hcomponent :
        (binaryListCode rationalEntryBinaryCode row).length ≤
          word.length := by
      simpa only [word, machinePairSecond_pair] using!
        machinePairSecond_length_le word
    exact (binaryListCode_listLength_le rationalEntryBinaryCode row).trans
      hcomponent
  have hentry : ∀ q ∈ row,
      (rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat q).div scale))).length ≤
          64 + 72 * word.length := by
    intro q hq
    have hqCode := binaryListCode_element_length_le
      rationalEntryBinaryCode hq
    have hqWidth : rawRatWidth (rawRatOfRat q) ≤ word.length := by
      have hentryCode :
          (rawRatBinaryCode (rawRatOfRat q)).length ≤
            (binaryListCode rationalEntryBinaryCode row).length := by
        simpa only [rawRatBinaryCode_rawRatOfRat] using! hqCode
      have hrowCode :
          (binaryListCode rationalEntryBinaryCode row).length ≤
            word.length := by
        simpa only [word, machinePairSecond_pair] using!
          machinePairSecond_length_le word
      exact (rawRatWidth_le_binaryCode_length (rawRatOfRat q)).trans
        (hentryCode.trans hrowCode)
    have hdiv := rawRatWidth_div_le (rawRatOfRat q) scale
    have hnormalize :=
      rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
        ((rawRatOfRat q).div scale)
    omega
  rw [binaryListCode_length_eq_sum]
  have hterm : ∀ value ∈
      ((row.map fun q ↦ binaryNormalizeRawRat
          ((rawRatOfRat q).div scale)).map
        fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2),
      value ≤ 130 + 144 * word.length := by
    simp only [List.map_map]
    intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨q, hq, rfl⟩
    have := hentry q hq
    simp only [Function.comp_apply]
    omega
  have hsum := natList_sum_le_length_mul hterm
  simp only [List.length_map] at hsum
  have hpoly :
      word.length * (130 + 144 * word.length) ≤
        (machineRationalRowDivideInputBound word).length := by
    simp only [machineRationalRowDivideInputBound,
      machineBinaryMulWidth,
      List.length_replicate, List.length_append]
    rw [machineRationalRowDividePadSixteen_length]
    nlinarith [sq_nonneg word.length]
  exact hsum.trans <| (Nat.mul_le_mul_right _ hrowLength).trans hpoly

/-! ## Exact semantics -/

/-- Divides each rational row entry by the raw scale and normalizes each resulting raw fraction. -/
def rationalRowDivideValues (scale : RawRat) (row : List ℚ) : List ℚ :=
  row.map fun q ↦ binaryNormalizeRawRat ((rawRatOfRat q).div scale)

/-- Encodes a raw divisor paired with the rational row to divide. -/
def machineRationalRowDivideCanonicalInput
    (scale : RawRat) (row : List ℚ) : List Bool :=
  pair (rawRatBinaryCode scale)
    (binaryListCode rationalEntryBinaryCode row)

/-- Encodes the unprocessed row suffix and reversed divided prefix after `k` entries, preserving
divisor and bound. -/
def machineRationalRowDivideSemanticState
    (scale : RawRat) (row : List ℚ) (k : ℕ) : List Bool :=
  let output := rationalRowDivideValues scale row
  let word := machineRationalRowDivideCanonicalInput scale row
  machineRationalRowDividePack
    (binaryListCode rationalEntryBinaryCode (row.drop k))
    (binaryListCode rationalEntryBinaryCode (output.take k).reverse)
    (rawRatBinaryCode scale)
    (machineRationalRowDivideInputBound word)

theorem machineRationalRowDivideInit_semantics
    (scale : RawRat) (row : List ℚ) :
    machineRationalRowDivideInit
        (machineRationalRowDivideCanonicalInput scale row) =
      machineRationalRowDivideSemanticState scale row 0 := by
  simp [machineRationalRowDivideInit,
    machineRationalRowDivideCanonicalInput,
    machineRationalRowDivideSemanticState,
    machineRationalRowDivideRow, machineRationalRowDivideScale,
    binaryListCode]

theorem machineRationalRowDivideEntry_semantics
    (scale : RawRat) (row : List ℚ) (k : ℕ) (hk : k < row.length) :
    machineRationalRowDivideEntry
        (machineRationalRowDivideSemanticState scale row k) =
      rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat row[k]).div scale)) := by
  have hdrop := List.drop_eq_getElem_cons hk
  rw [machineRationalRowDivideEntry,
    machineRationalRowDivideRawEntry]
  simp only [machineRationalRowDivideSemanticState,
    machineRationalRowDivideRemaining_pack,
    machineRationalRowDivideScaleField_pack, hdrop,
    machineListHead_cons, ← rawRatBinaryCode_rawRatOfRat,
    machineRawRatDivCode_encode,
    machineNormalizeRawRatEntryCode_encode]

theorem machineRationalRowDivideStep_semantics
    (scale : RawRat) (row : List ℚ) (k : ℕ) (hk : k < row.length) :
    machineRationalRowDivideStep
        (machineRationalRowDivideSemanticState scale row k) =
      machineRationalRowDivideSemanticState scale row (k + 1) := by
  let output := rationalRowDivideValues scale row
  let word := machineRationalRowDivideCanonicalInput scale row
  have houtputLength : output.length = row.length := by
    simp [output, rationalRowDivideValues]
  have hkoutput : k < output.length := by omega
  have houtputGet : output[k] =
      binaryNormalizeRawRat ((rawRatOfRat row[k]).div scale) := by
    simp [output, rationalRowDivideValues, List.getElem_map]
  have hdrop := List.drop_eq_getElem_cons hk
  have htake := List.take_concat_get hkoutput
  have hprefix : (output.take (k + 1)).reverse =
      output[k] :: (output.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := output.take k) (a := output[k]))
  have hfullBound :
      (binaryListCode rationalEntryBinaryCode output).length ≤
        (machineRationalRowDivideInputBound word).length := by
    simpa only [word, output, machineRationalRowDivideCanonicalInput,
      rationalRowDivideValues] using!
      machineRationalRowDivide_output_length_le_bound scale row
  have hprefixLength :
      (binaryListCode rationalEntryBinaryCode
        (output.take (k + 1)).reverse).length ≤
          (machineRationalRowDivideInputBound word).length :=
    (binaryListCode_take_reverse_length_le rationalEntryBinaryCode
      output (k + 1)).trans hfullBound
  have htakeBound :
      (binaryListCode rationalEntryBinaryCode
          (output.take (k + 1)).reverse).take
            (machineRationalRowDivideInputBound word).length =
        binaryListCode rationalEntryBinaryCode
          (output.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hnonempty :
      binaryListCode rationalEntryBinaryCode (row.drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil _ _ _
  rw [machineRationalRowDivideStep]
  simp only [machineRationalRowDivideSemanticState,
    machineRationalRowDivideRemaining_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hnonempty,
    machineRationalRowDivideAdvance]
  simp only [machineRationalRowDivideRemaining_pack,
    machineRationalRowDivideAccumulator_pack,
    machineRationalRowDivideScaleField_pack,
    machineRationalRowDivideBound_pack,
    machineRationalRowDivideNextAccumulator,
    machineRationalRowDivideCandidate]
  have hentry :
      machineRationalRowDivideEntry
          (machineRationalRowDividePack
            (binaryListCode rationalEntryBinaryCode (row.drop k))
            (binaryListCode rationalEntryBinaryCode
              (output.take k).reverse)
            (rawRatBinaryCode scale)
            (machineRationalRowDivideInputBound word)) =
        rationalEntryBinaryCode output[k] := by
    rw [houtputGet]
    simpa only [machineRationalRowDivideSemanticState, output, word] using!
      machineRationalRowDivideEntry_semantics scale row k hk
  rw [hentry]
  rw [hdrop, machineListTail_cons]
  change machineRationalRowDividePack
      (binaryListCode rationalEntryBinaryCode (row.drop (k + 1)))
      ((binaryListCode rationalEntryBinaryCode
        (output[k] :: (output.take k).reverse)).take
          (machineRationalRowDivideInputBound word).length)
      (rawRatBinaryCode scale)
      (machineRationalRowDivideInputBound word) = _
  rw [← hprefix, htakeBound]

theorem machineRationalRowDivideIterate_semantics
    (scale : RawRat) (row : List ℚ) : ∀ k ≤ row.length,
    (machineRationalRowDivideStep)^[k]
        (machineRationalRowDivideInit
          (machineRationalRowDivideCanonicalInput scale row)) =
      machineRationalRowDivideSemanticState scale row k := by
  intro k hk
  induction k with
  | zero => exact machineRationalRowDivideInit_semantics scale row
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalRowDivideStep_semantics scale row k (by omega)

theorem machineRationalRowDivide_done_iterate
    (extra : ℕ) (accumulator scale bound : List Bool) :
    (machineRationalRowDivideStep)^[extra]
        (machineRationalRowDividePack [] accumulator scale bound) =
      machineRationalRowDividePack [] accumulator scale bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalRowDivideStep]

theorem machineRationalRowDivideFinalState_encode
    (scale : RawRat) (row : List ℚ) :
    machineRationalRowDivideFinalState
        (machineRationalRowDivideCanonicalInput scale row) =
      machineRationalRowDividePack []
        (binaryListCode rationalEntryBinaryCode
          (rationalRowDivideValues scale row).reverse)
        (rawRatBinaryCode scale)
        (machineRationalRowDivideInputBound
          (machineRationalRowDivideCanonicalInput scale row)) := by
  let word := machineRationalRowDivideCanonicalInput scale row
  have hrowLength : row.length ≤ word.length := by
    have hcomponent :
        (binaryListCode rationalEntryBinaryCode row).length ≤
          word.length := by
      simpa only [word, machineRationalRowDivideCanonicalInput,
        machinePairSecond_pair] using!
        (show (machinePairSecond word).length ≤ word.length from
          machinePairSecond_length_le word)
    exact (binaryListCode_listLength_le rationalEntryBinaryCode row).trans
      hcomponent
  have htakeAll :
      (rationalRowDivideValues scale row).take row.length =
        rationalRowDivideValues scale row := by
    have hlength : (rationalRowDivideValues scale row).length =
        row.length := by simp [rationalRowDivideValues]
    rw [← hlength, List.take_length]
  have hsplit : word.length =
      (word.length - row.length) + row.length := by omega
  change (machineRationalRowDivideStep)^[word.length]
      (machineRationalRowDivideInit word) = _
  rw [hsplit, Function.iterate_add_apply,
    machineRationalRowDivideIterate_semantics scale row row.length le_rfl]
  simp only [machineRationalRowDivideSemanticState, List.drop_length,
    binaryListCode, word]
  rw [htakeAll]
  rw [machineRationalRowDivide_done_iterate]

@[simp] theorem machineRationalRowDivide_encode
    (scale : RawRat) (row : List ℚ) :
    machineRationalRowDivide
        (machineRationalRowDivideCanonicalInput scale row) =
      binaryListCode rationalEntryBinaryCode
        (rationalRowDivideValues scale row) := by
  rw [machineRationalRowDivide,
    machineRationalRowDivideFinalState_encode]
  simp only [machineRationalRowDivideAccumulator_pack,
    machineListReverse_encode, List.reverse_reverse]

end BeyondBethe
