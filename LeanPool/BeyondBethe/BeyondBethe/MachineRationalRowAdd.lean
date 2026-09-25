/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse
public import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalArithmetic
public import Mathlib.Tactic

/-!
# Adding every entry of a rational row by one raw rational

The input is `pair deltaRawCode rowCode`.  Each output entry is normalized to
the numerator/denominator pair encoding required inside rational matrices.
This is deliberately not `machineRationalDivCode`, whose public output uses a
different one-natural encoding.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the fixed raw increment from a row-addition request. -/
def machineRationalRowAddDelta (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the encoded rational row from a row-addition request. -/
def machineRationalRowAddRow (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Concatenates two copies of a word for row-addition width padding. -/
def machineRationalRowAddPadTwo (word : List Bool) : List Bool :=
  word ++ word

/-- Concatenates four copies of a word for row-addition width padding. -/
def machineRationalRowAddPadFour (word : List Bool) : List Bool :=
  machineRationalRowAddPadTwo word ++ machineRationalRowAddPadTwo word

/-- Concatenates eight copies of a word for row-addition width padding. -/
def machineRationalRowAddPadEight (word : List Bool) : List Bool :=
  machineRationalRowAddPadFour word ++ machineRationalRowAddPadFour word

/-- Concatenates sixteen copies of a word for row-addition width padding. -/
def machineRationalRowAddPadSixteen (word : List Bool) : List Bool :=
  machineRationalRowAddPadEight word ++ machineRationalRowAddPadEight word

/-- A coefficient-adjusted quadratic envelope.  Sixteen copies before the
standard square provide enough room for every normalized output entry without
the impractical quartic padding used by an earlier draft. -/
def machineRationalRowAddInputBound (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineRationalRowAddPadSixteen word)

/-- Packs the unprocessed row, reversed output accumulator, fixed increment, and bound for row
addition. -/
def machineRationalRowAddPack
    (remaining accumulator delta bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair delta bound))

/-- Extracts the unprocessed encoded row from a row-addition state. -/
def machineRationalRowAddRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the reverse-order output accumulator from a row-addition state. -/
def machineRationalRowAddAccumulator (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the fixed raw increment from a row-addition state. -/
def machineRationalRowAddDeltaField (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the accumulator length-bound word from a row-addition state. -/
def machineRationalRowAddBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

/-- Adds the fixed increment to the next row entry in raw rational arithmetic. -/
def machineRationalRowAddRawEntry (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineListHead (machineRationalRowAddRemaining state))
      (machineRationalRowAddDeltaField state))

/-- Normalizes the updated row entry into its rational entry encoding. -/
def machineRationalRowAddEntry (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRationalRowAddRawEntry state)

/-- Prepends the normalized updated entry to the reverse-order output accumulator. -/
def machineRationalRowAddCandidate (state : List Bool) : List Bool :=
  pair (machineRationalRowAddEntry state)
    (machineRationalRowAddAccumulator state)

/-- Truncates the candidate row-addition accumulator to the stored bound length. -/
def machineRationalRowAddNextAccumulator (state : List Bool) : List Bool :=
  (machineRationalRowAddCandidate state).take
    (machineRationalRowAddBound state).length

/-- Consumes the next row entry and stores the bounded updated accumulator, preserving increment
and bound. -/
def machineRationalRowAddAdvance (state : List Bool) : List Bool :=
  machineRationalRowAddPack
    (machineListTail (machineRationalRowAddRemaining state))
    (machineRationalRowAddNextAccumulator state)
    (machineRationalRowAddDeltaField state)
    (machineRationalRowAddBound state)

/-- Fixes an exhausted row-addition state and otherwise processes one entry. -/
def machineRationalRowAddStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalRowAddRemaining state) state
    (machineRationalRowAddAdvance state)

/-- Initializes row addition with the requested row, empty accumulator, fixed increment, and
computed bound. -/
def machineRationalRowAddInit (word : List Bool) : List Bool :=
  machineRationalRowAddPack (machineRationalRowAddRow word) []
    (machineRationalRowAddDelta word)
    (machineRationalRowAddInputBound word)

/-- Packs input and bound words in the four-field layout to bound the row-addition state. -/
def machineRationalRowAddWidth (word : List Bool) : List Bool :=
  let bound := machineRationalRowAddInputBound word
  machineRationalRowAddPack word bound word bound

/-- Runs the row-addition scan once per input bit from its initial state. -/
def machineRationalRowAddFinalState (word : List Bool) : List Bool :=
  (machineRationalRowAddStep)^[word.length]
    (machineRationalRowAddInit word)

/-- Reverses the final accumulator to return the incremented rational row in its original order. -/
def machineRationalRowAdd (word : List Bool) : List Bool :=
  machineListReverse
    (machineRationalRowAddAccumulator
      (machineRationalRowAddFinalState word))

theorem machineRationalRowAddDelta_mem_FP :
    machineRationalRowAddDelta ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRationalRowAddRow_mem_FP :
    machineRationalRowAddRow ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineRationalRowAddPadTwo_mem_FP :
    machineRationalRowAddPadTwo ∈ Complexity.FP :=
  machineAppend_mem_FP id_mem_FP id_mem_FP

theorem machineRationalRowAddPadFour_mem_FP :
    machineRationalRowAddPadFour ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowAddPadTwo_mem_FP
    machineRationalRowAddPadTwo_mem_FP

theorem machineRationalRowAddPadEight_mem_FP :
    machineRationalRowAddPadEight ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowAddPadFour_mem_FP
    machineRationalRowAddPadFour_mem_FP

theorem machineRationalRowAddPadSixteen_mem_FP :
    machineRationalRowAddPadSixteen ∈ Complexity.FP :=
  machineAppend_mem_FP machineRationalRowAddPadEight_mem_FP
    machineRationalRowAddPadEight_mem_FP

theorem machineRationalRowAddInputBound_mem_FP :
    machineRationalRowAddInputBound ∈ Complexity.FP := by
  simpa only [machineRationalRowAddInputBound] using!
    machineCompose_mem_FP machineRationalRowAddPadSixteen_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineRationalRowAddPadSixteen_length (word : List Bool) :
    (machineRationalRowAddPadSixteen word).length = 16 * word.length := by
  simp only [machineRationalRowAddPadSixteen,
    machineRationalRowAddPadEight,
    machineRationalRowAddPadFour,
    machineRationalRowAddPadTwo, List.length_append]
  omega

theorem machineRationalRowAddInputBound_length_mono
    {left right : List Bool} (h : left.length ≤ right.length) :
    (machineRationalRowAddInputBound left).length ≤
      (machineRationalRowAddInputBound right).length := by
  apply machineBinaryMulWidth_length_mono
  rw [machineRationalRowAddPadSixteen_length,
    machineRationalRowAddPadSixteen_length]
  exact Nat.mul_le_mul_left 16 h

theorem machineRationalRowAddRemaining_mem_FP :
    machineRationalRowAddRemaining ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRationalRowAddAccumulator_mem_FP :
    machineRationalRowAddAccumulator ∈ Complexity.FP := by
  simpa only [machineRationalRowAddAccumulator] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalRowAddDeltaField_mem_FP :
    machineRationalRowAddDeltaField ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineRationalRowAddDeltaField] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineRationalRowAddBound_mem_FP :
    machineRationalRowAddBound ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineRationalRowAddBound] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineRationalRowAddRawEntry_mem_FP :
    machineRationalRowAddRawEntry ∈ Complexity.FP := by
  have hhead := machineCompose_mem_FP machineRationalRowAddRemaining_mem_FP
    machineListHead_mem_FP
  have hinput := machinePair_mem_FP hhead
    machineRationalRowAddDeltaField_mem_FP
  simpa only [machineRationalRowAddRawEntry] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineRationalRowAddEntry_mem_FP :
    machineRationalRowAddEntry ∈ Complexity.FP := by
  simpa only [machineRationalRowAddEntry] using!
    machineCompose_mem_FP machineRationalRowAddRawEntry_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineRationalRowAddCandidate_mem_FP :
    machineRationalRowAddCandidate ∈ Complexity.FP :=
  machinePair_mem_FP machineRationalRowAddEntry_mem_FP
    machineRationalRowAddAccumulator_mem_FP

theorem machineRationalRowAddNextAccumulator_mem_FP :
    machineRationalRowAddNextAccumulator ∈ Complexity.FP := by
  simpa only [machineRationalRowAddNextAccumulator] using!
    machineTake_mem_FP machineRationalRowAddBound_mem_FP
      machineRationalRowAddCandidate_mem_FP

theorem machineRationalRowAddAdvance_mem_FP :
    machineRationalRowAddAdvance ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP machineRationalRowAddRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalRowAddNextAccumulator_mem_FP
      (machinePair_mem_FP machineRationalRowAddDeltaField_mem_FP
        machineRationalRowAddBound_mem_FP))

theorem machineRationalRowAddStep_mem_FP :
    machineRationalRowAddStep ∈ Complexity.FP := by
  exact machineIfEmpty_mem_FP machineRationalRowAddRemaining_mem_FP
    id_mem_FP machineRationalRowAddAdvance_mem_FP

theorem machineRationalRowAddInit_mem_FP :
    machineRationalRowAddInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRationalRowAddRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineRationalRowAddDelta_mem_FP
        machineRationalRowAddInputBound_mem_FP))

theorem machineRationalRowAddWidth_mem_FP :
    machineRationalRowAddWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP machineRationalRowAddInputBound_mem_FP
      (machinePair_mem_FP id_mem_FP
        machineRationalRowAddInputBound_mem_FP))

@[simp] theorem machineRationalRowAddRemaining_pack (a b c d) :
    machineRationalRowAddRemaining
      (machineRationalRowAddPack a b c d) = a := by
  simp [machineRationalRowAddRemaining, machineRationalRowAddPack]

@[simp] theorem machineRationalRowAddAccumulator_pack (a b c d) :
    machineRationalRowAddAccumulator
      (machineRationalRowAddPack a b c d) = b := by
  simp [machineRationalRowAddAccumulator, machineRationalRowAddPack]

@[simp] theorem machineRationalRowAddDeltaField_pack (a b c d) :
    machineRationalRowAddDeltaField
      (machineRationalRowAddPack a b c d) = c := by
  simp [machineRationalRowAddDeltaField, machineRationalRowAddPack]

@[simp] theorem machineRationalRowAddBound_pack (a b c d) :
    machineRationalRowAddBound
      (machineRationalRowAddPack a b c d) = d := by
  simp [machineRationalRowAddBound, machineRationalRowAddPack]

/-- Requires exact row-addition state packing, input-bounded remaining row and increment, a
bounded accumulator, and the prescribed bound word. -/
def MachineRationalRowAddStateBound (word state : List Bool) : Prop :=
  state = machineRationalRowAddPack
      (machineRationalRowAddRemaining state)
      (machineRationalRowAddAccumulator state)
      (machineRationalRowAddDeltaField state)
      (machineRationalRowAddBound state) ∧
    (machineRationalRowAddRemaining state).length ≤ word.length ∧
    (machineRationalRowAddAccumulator state).length ≤
      (machineRationalRowAddInputBound word).length ∧
    (machineRationalRowAddDeltaField state).length ≤ word.length ∧
    machineRationalRowAddBound state =
      machineRationalRowAddInputBound word

theorem machineRationalRowAddInit_bound (word : List Bool) :
    MachineRationalRowAddStateBound word
      (machineRationalRowAddInit word) := by
  simp only [MachineRationalRowAddStateBound,
    machineRationalRowAddInit,
    machineRationalRowAddRemaining_pack,
    machineRationalRowAddAccumulator_pack,
    machineRationalRowAddDeltaField_pack,
    machineRationalRowAddBound_pack]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineRationalRowAddRow] using!
      machinePairSecond_length_le word
  · simpa only [machineRationalRowAddDelta] using!
      machinePairFirst_length_le word

theorem machineRationalRowAddStep_bound {word state : List Bool}
    (hstate : MachineRationalRowAddStateBound word state) :
    MachineRationalRowAddStateBound word
      (machineRationalRowAddStep state) := by
  rcases hstate with
    ⟨hdecomp, hremaining, haccumulator, hdelta, hbound⟩
  by_cases hnil : machineRationalRowAddRemaining state = []
  · rw [machineRationalRowAddStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, haccumulator, hdelta, hbound⟩
  · rw [machineRationalRowAddStep]
    cases hremainingCode : machineRationalRowAddRemaining state with
    | nil => exact False.elim (hnil hremainingCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineRationalRowAddAdvance]
        simp only [MachineRationalRowAddStateBound,
          machineRationalRowAddRemaining_pack,
          machineRationalRowAddAccumulator_pack,
          machineRationalRowAddDeltaField_pack,
          machineRationalRowAddBound_pack]
        refine ⟨trivial, ?_, ?_, hdelta, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalRowAddRemaining state)).trans hremaining
        · rw [machineRationalRowAddNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalRowAddIterate_bound (word : List Bool) : ∀ k,
    MachineRationalRowAddStateBound word
      ((machineRationalRowAddStep)^[k]
        (machineRationalRowAddInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalRowAddInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalRowAddStep_bound ih

theorem machineRationalRowAddIterate_length_le_width
    (word : List Bool) (iterations : ℕ) (_ : iterations ≤ word.length) :
    ((machineRationalRowAddStep)^[iterations]
      (machineRationalRowAddInit word)).length ≤
        (machineRationalRowAddWidth word).length := by
  rcases machineRationalRowAddIterate_bound word iterations with
    ⟨hdecomp, hremaining, haccumulator, hdelta, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalRowAddPack,
    machineRationalRowAddWidth, pair_length]
  omega

theorem machineRationalRowAddFinalState_mem_FP :
    machineRationalRowAddFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineRationalRowAddStep_mem_FP
    machineRationalRowAddInit_mem_FP id_mem_FP
    machineRationalRowAddWidth_mem_FP
    machineRationalRowAddIterate_length_le_width

theorem machineRationalRowAdd_mem_FP :
    machineRationalRowAdd ∈ Complexity.FP := by
  have hacc := machineCompose_mem_FP
    machineRationalRowAddFinalState_mem_FP
    machineRationalRowAddAccumulator_mem_FP
  simpa only [machineRationalRowAdd] using!
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

theorem machineRationalRowAdd_output_length_le_bound
    (delta : RawRat) (row : List ℚ) :
    let word := pair (rawRatBinaryCode delta)
      (binaryListCode rationalEntryBinaryCode row)
    let output := row.map fun q ↦
      binaryNormalizeRawRat ((rawRatOfRat q).add delta)
    (binaryListCode rationalEntryBinaryCode output).length ≤
      (machineRationalRowAddInputBound word).length := by
  dsimp only
  let word := pair (rawRatBinaryCode delta)
    (binaryListCode rationalEntryBinaryCode row)
  have hdelta : rawRatWidth delta ≤ word.length := by
    have hcomponent : (rawRatBinaryCode delta).length ≤ word.length := by
      simpa only [word, machinePairFirst_pair] using!
        machinePairFirst_length_le word
    exact (rawRatWidth_le_binaryCode_length delta).trans
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
        (binaryNormalizeRawRat ((rawRatOfRat q).add delta))).length ≤
          100 + 72 * word.length := by
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
    have hdiv := rawRatWidth_add_le (rawRatOfRat q) delta
    have hnormalize :=
      rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
        ((rawRatOfRat q).add delta)
    omega
  rw [binaryListCode_length_eq_sum]
  have hterm : ∀ value ∈
      ((row.map fun q ↦ binaryNormalizeRawRat
          ((rawRatOfRat q).add delta)).map
        fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2),
      value ≤ 202 + 144 * word.length := by
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
      word.length * (202 + 144 * word.length) ≤
        (machineRationalRowAddInputBound word).length := by
    simp only [machineRationalRowAddInputBound,
      machineBinaryMulWidth,
      List.length_replicate, List.length_append]
    rw [machineRationalRowAddPadSixteen_length]
    nlinarith [sq_nonneg word.length]
  exact hsum.trans <| (Nat.mul_le_mul_right _ hrowLength).trans hpoly

/-! ## Exact semantics -/

/-- Adds the raw increment to each rational row entry and normalizes each resulting raw
fraction. -/
def rationalRowAddValues (delta : RawRat) (row : List ℚ) : List ℚ :=
  row.map fun q ↦ binaryNormalizeRawRat ((rawRatOfRat q).add delta)

def machineRationalRowAddCanonicalInput
    (delta : RawRat) (row : List ℚ) : List Bool :=
  pair (rawRatBinaryCode delta)
    (binaryListCode rationalEntryBinaryCode row)

def machineRationalRowAddSemanticState
    (delta : RawRat) (row : List ℚ) (k : ℕ) : List Bool :=
  let output := rationalRowAddValues delta row
  let word := machineRationalRowAddCanonicalInput delta row
  machineRationalRowAddPack
    (binaryListCode rationalEntryBinaryCode (row.drop k))
    (binaryListCode rationalEntryBinaryCode (output.take k).reverse)
    (rawRatBinaryCode delta)
    (machineRationalRowAddInputBound word)

theorem machineRationalRowAddInit_semantics
    (delta : RawRat) (row : List ℚ) :
    machineRationalRowAddInit
        (machineRationalRowAddCanonicalInput delta row) =
      machineRationalRowAddSemanticState delta row 0 := by
  simp [machineRationalRowAddInit,
    machineRationalRowAddCanonicalInput,
    machineRationalRowAddSemanticState,
    machineRationalRowAddRow, machineRationalRowAddDelta,
    binaryListCode]

theorem machineRationalRowAddEntry_semantics
    (delta : RawRat) (row : List ℚ) (k : ℕ) (hk : k < row.length) :
    machineRationalRowAddEntry
        (machineRationalRowAddSemanticState delta row k) =
      rationalEntryBinaryCode
        (binaryNormalizeRawRat ((rawRatOfRat row[k]).add delta)) := by
  have hdrop := List.drop_eq_getElem_cons hk
  rw [machineRationalRowAddEntry,
    machineRationalRowAddRawEntry]
  simp only [machineRationalRowAddSemanticState,
    machineRationalRowAddRemaining_pack,
    machineRationalRowAddDeltaField_pack, hdrop,
    machineListHead_cons, ← rawRatBinaryCode_rawRatOfRat,
    machineRawRatAddCode_encode,
    machineNormalizeRawRatEntryCode_encode]

theorem machineRationalRowAddStep_semantics
    (delta : RawRat) (row : List ℚ) (k : ℕ) (hk : k < row.length) :
    machineRationalRowAddStep
        (machineRationalRowAddSemanticState delta row k) =
      machineRationalRowAddSemanticState delta row (k + 1) := by
  let output := rationalRowAddValues delta row
  let word := machineRationalRowAddCanonicalInput delta row
  have houtputLength : output.length = row.length := by
    simp [output, rationalRowAddValues]
  have hkoutput : k < output.length := by omega
  have houtputGet : output[k] =
      binaryNormalizeRawRat ((rawRatOfRat row[k]).add delta) := by
    simp [output, rationalRowAddValues, List.getElem_map]
  have hdrop := List.drop_eq_getElem_cons hk
  have htake := List.take_concat_get hkoutput
  have hprefix : (output.take (k + 1)).reverse =
      output[k] :: (output.take k).reverse := by
    rw [← htake]
    simpa only [List.concat_eq_append] using!
      (List.reverse_concat (l := output.take k) (a := output[k]))
  have hfullBound :
      (binaryListCode rationalEntryBinaryCode output).length ≤
        (machineRationalRowAddInputBound word).length := by
    simpa only [word, output, machineRationalRowAddCanonicalInput,
      rationalRowAddValues] using!
      machineRationalRowAdd_output_length_le_bound delta row
  have hprefixLength :
      (binaryListCode rationalEntryBinaryCode
        (output.take (k + 1)).reverse).length ≤
          (machineRationalRowAddInputBound word).length :=
    (binaryListCode_take_reverse_length_le rationalEntryBinaryCode
      output (k + 1)).trans hfullBound
  have htakeBound :
      (binaryListCode rationalEntryBinaryCode
          (output.take (k + 1)).reverse).take
            (machineRationalRowAddInputBound word).length =
        binaryListCode rationalEntryBinaryCode
          (output.take (k + 1)).reverse :=
    List.take_of_length_le hprefixLength
  have hnonempty :
      binaryListCode rationalEntryBinaryCode (row.drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil _ _ _
  rw [machineRationalRowAddStep]
  simp only [machineRationalRowAddSemanticState,
    machineRationalRowAddRemaining_pack]
  rw [machineIfEmpty_of_ne_nil _ _ _ hnonempty,
    machineRationalRowAddAdvance]
  simp only [machineRationalRowAddRemaining_pack,
    machineRationalRowAddAccumulator_pack,
    machineRationalRowAddDeltaField_pack,
    machineRationalRowAddBound_pack,
    machineRationalRowAddNextAccumulator,
    machineRationalRowAddCandidate]
  have hentry :
      machineRationalRowAddEntry
          (machineRationalRowAddPack
            (binaryListCode rationalEntryBinaryCode (row.drop k))
            (binaryListCode rationalEntryBinaryCode
              (output.take k).reverse)
            (rawRatBinaryCode delta)
            (machineRationalRowAddInputBound word)) =
        rationalEntryBinaryCode output[k] := by
    rw [houtputGet]
    simpa only [machineRationalRowAddSemanticState, output, word] using!
      machineRationalRowAddEntry_semantics delta row k hk
  rw [hentry]
  rw [hdrop, machineListTail_cons]
  change machineRationalRowAddPack
      (binaryListCode rationalEntryBinaryCode (row.drop (k + 1)))
      ((binaryListCode rationalEntryBinaryCode
        (output[k] :: (output.take k).reverse)).take
          (machineRationalRowAddInputBound word).length)
      (rawRatBinaryCode delta)
      (machineRationalRowAddInputBound word) = _
  rw [← hprefix, htakeBound]

theorem machineRationalRowAddIterate_semantics
    (delta : RawRat) (row : List ℚ) : ∀ k ≤ row.length,
    (machineRationalRowAddStep)^[k]
        (machineRationalRowAddInit
          (machineRationalRowAddCanonicalInput delta row)) =
      machineRationalRowAddSemanticState delta row k := by
  intro k hk
  induction k with
  | zero => exact machineRationalRowAddInit_semantics delta row
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalRowAddStep_semantics delta row k (by omega)

theorem machineRationalRowAdd_done_iterate
    (extra : ℕ) (accumulator delta bound : List Bool) :
    (machineRationalRowAddStep)^[extra]
        (machineRationalRowAddPack [] accumulator delta bound) =
      machineRationalRowAddPack [] accumulator delta bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalRowAddStep]

theorem machineRationalRowAddFinalState_encode
    (delta : RawRat) (row : List ℚ) :
    machineRationalRowAddFinalState
        (machineRationalRowAddCanonicalInput delta row) =
      machineRationalRowAddPack []
        (binaryListCode rationalEntryBinaryCode
          (rationalRowAddValues delta row).reverse)
        (rawRatBinaryCode delta)
        (machineRationalRowAddInputBound
          (machineRationalRowAddCanonicalInput delta row)) := by
  let word := machineRationalRowAddCanonicalInput delta row
  have hrowLength : row.length ≤ word.length := by
    have hcomponent :
        (binaryListCode rationalEntryBinaryCode row).length ≤
          word.length := by
      simpa only [word, machineRationalRowAddCanonicalInput,
        machinePairSecond_pair] using!
        (show (machinePairSecond word).length ≤ word.length from
          machinePairSecond_length_le word)
    exact (binaryListCode_listLength_le rationalEntryBinaryCode row).trans
      hcomponent
  have htakeAll :
      (rationalRowAddValues delta row).take row.length =
        rationalRowAddValues delta row := by
    have hlength : (rationalRowAddValues delta row).length =
        row.length := by simp [rationalRowAddValues]
    rw [← hlength, List.take_length]
  have hsplit : word.length =
      (word.length - row.length) + row.length := by omega
  change (machineRationalRowAddStep)^[word.length]
      (machineRationalRowAddInit word) = _
  rw [hsplit, Function.iterate_add_apply,
    machineRationalRowAddIterate_semantics delta row row.length le_rfl]
  simp only [machineRationalRowAddSemanticState, List.drop_length,
    binaryListCode, word]
  rw [htakeAll]
  rw [machineRationalRowAdd_done_iterate]

@[simp] theorem machineRationalRowAdd_encode
    (delta : RawRat) (row : List ℚ) :
    machineRationalRowAdd
        (machineRationalRowAddCanonicalInput delta row) =
      binaryListCode rationalEntryBinaryCode
        (rationalRowAddValues delta row) := by
  rw [machineRationalRowAdd,
    machineRationalRowAddFinalState_encode]
  simp only [machineRationalRowAddAccumulator_pack,
    machineListReverse_encode, List.reverse_reverse]

end BeyondBethe
