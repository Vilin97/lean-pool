/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerSignedMagnitude
import LeanPool.BeyondBethe.BeyondBethe.MachineLengthBits
import LeanPool.BeyondBethe.BeyondBethe.RationalEncodingBounds

/-!
# Exact unary lengths for optimizer matrix entries

The optimizer schedules use `encodedBitLength ℚ q`, not merely the length of
the machine-facing rational-entry word.  This module computes that quantity
exactly from the numerator and denominator subwords.  Producing a unary ruler
is the useful form: every later precision loop consumes its schedule in unary.
-/

namespace BeyondBethe

open Complexity

def boolDataSize : Bool → ℕ
  | false => 2
  | true => 4

def boolDataLength (word : List Bool) : ℕ :=
  (word.map boolDataSize).sum

def boolDataRuler (word : List Bool) : List Bool :=
  word.flatMap fun bit ↦ List.replicate (boolDataSize bit) true

@[simp] theorem boolDataRuler_length (word : List Bool) :
    (boolDataRuler word).length = boolDataLength word := by
  simp [boolDataRuler, boolDataLength]

theorem boolDataRuler_eq_replicate (word : List Bool) :
    boolDataRuler word = List.replicate (boolDataLength word) true := by
  induction word with
  | nil => simp [boolDataRuler, boolDataLength]
  | cons bit word ih =>
      change List.replicate (boolDataSize bit) true ++ boolDataRuler word = _
      rw [ih, ← List.replicate_add]
      congr 1

theorem boolDataLength_le_four_mul_length (word : List Bool) :
    boolDataLength word ≤ 4 * word.length := by
  induction word with
  | nil => simp [boolDataLength]
  | cons bit word ih =>
      change boolDataSize bit + boolDataLength word ≤
        4 * (word.length + 1)
      cases bit <;> simp [boolDataSize] <;> omega

theorem bool_dataEncode_size_eq (b : Bool) :
    (DataEncode.encode b).size = boolDataSize b := by
  cases b <;> norm_num [DataEncode.encode, Data.size, boolDataSize]

theorem nat_encodedBitLength_eq_boolDataLength (n : ℕ) :
    encodedBitLength ℕ n = 2 + boolDataLength n.bits := by
  rw [encodedBitLength_eq_dataSize]
  change (Data.l (n.bits.map fun b ↦ DataEncode.encode b)).size = _
  rw [Data.size]
  unfold boolDataLength
  congr 1
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact bool_dataEncode_size_eq b

theorem integer_encodedBitLength_eq_boolDataLength (z : ℤ) :
    encodedBitLength ℤ z =
      4 + boolDataSize (integerPayload z).1 +
        boolDataLength z.natAbs.bits := by
  rw [encodedBitLength_eq_dataSize]
  change (DataEncode.encode (integerPayload z)).size = _
  rw [show DataEncode.encode (integerPayload z) =
      Data.l [DataEncode.encode (integerPayload z).1,
        DataEncode.encode (integerPayload z).2] by
      exact DataEncode_pair _ _]
  simp only [Data.size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, bool_dataEncode_size_eq]
  rw [← encodedBitLength_eq_dataSize,
    nat_encodedBitLength_eq_boolDataLength, integerPayload_snd]
  omega

theorem rational_encodedBitLength_eq_boolDataLength (q : ℚ) :
    encodedBitLength ℚ q =
      8 + boolDataSize (integerPayload q.num).1 +
        boolDataLength q.num.natAbs.bits + boolDataLength q.den.bits := by
  rw [encodedBitLength_eq_dataSize]
  change (DataEncode.encode (rationalPayload q)).size = _
  rw [show DataEncode.encode (rationalPayload q) =
      Data.l [DataEncode.encode q.num, DataEncode.encode q.den] by
      simpa only [rationalPayload] using! DataEncode_pair q.num q.den]
  simp only [Data.size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [← encodedBitLength_eq_dataSize,
    ← encodedBitLength_eq_dataSize,
    integer_encodedBitLength_eq_boolDataLength,
    nat_encodedBitLength_eq_boolDataLength]
  omega

/-! ## A finite-word transducer for `boolDataRuler` -/

def machineBoolDataPack (remaining acc : List Bool) : List Bool :=
  pair remaining acc

def machineBoolDataRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineBoolDataAcc (state : List Bool) : List Bool :=
  machinePairSecond state

def machineBoolDataBitRuler (state : List Bool) : List Bool :=
  machineIfHead (machineBoolDataRemaining state)
    (List.replicate 4 true) (List.replicate 2 true)

def machineBoolDataContinue (state : List Bool) : List Bool :=
  machineBoolDataPack (machineBoolDataRemaining state).tail
    (machineBoolDataAcc state ++ machineBoolDataBitRuler state)

def machineBoolDataStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineBoolDataRemaining state) state
    (machineBoolDataContinue state)

def machineBoolDataInit (word : List Bool) : List Bool :=
  machineBoolDataPack word []

def machineBoolDataBound (word : List Bool) : List Bool :=
  List.replicate 4 true ++
    (word ++ (word ++ (word ++ word)))

def machineBoolDataWidth (word : List Bool) : List Bool :=
  machineBoolDataPack (machineBoolDataBound word)
    (machineBoolDataBound word)

def machineBoolDataFinalState (word : List Bool) : List Bool :=
  (machineBoolDataStep)^[word.length] (machineBoolDataInit word)

def machineBoolDataLengthRuler (word : List Bool) : List Bool :=
  machineBoolDataAcc (machineBoolDataFinalState word)

theorem machineBoolDataRemaining_mem_FP :
    machineBoolDataRemaining ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineBoolDataAcc_mem_FP :
    machineBoolDataAcc ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineBoolDataBitRuler_mem_FP :
    machineBoolDataBitRuler ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineBoolDataRemaining_mem_FP
    (machineConst_mem_FP (List.replicate 4 true))
    (machineConst_mem_FP (List.replicate 2 true))

theorem machineBoolDataContinue_mem_FP :
    machineBoolDataContinue ∈ Complexity.FP := by
  have hremaining := machineCompose_mem_FP
    machineBoolDataRemaining_mem_FP machineTail_mem_FP
  have hacc := machineAppend_mem_FP machineBoolDataAcc_mem_FP
    machineBoolDataBitRuler_mem_FP
  exact machinePair_mem_FP hremaining hacc

theorem machineBoolDataStep_mem_FP :
    machineBoolDataStep ∈ Complexity.FP := by
  simpa only [machineBoolDataStep] using!
    machineIfEmpty_mem_FP machineBoolDataRemaining_mem_FP
      id_mem_FP machineBoolDataContinue_mem_FP

theorem machineBoolDataInit_mem_FP :
    machineBoolDataInit ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP (machineConst_mem_FP [])

theorem machineBoolDataBound_mem_FP :
    machineBoolDataBound ∈ Complexity.FP := by
  have hdouble := machineAppend_mem_FP id_mem_FP id_mem_FP
  have htriple := machineAppend_mem_FP id_mem_FP hdouble
  have hquadruple := machineAppend_mem_FP id_mem_FP htriple
  simpa only [machineBoolDataBound] using!
    machineAppend_mem_FP
      (machineConst_mem_FP (List.replicate 4 true)) hquadruple

theorem machineBoolDataWidth_mem_FP :
    machineBoolDataWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP machineBoolDataBound_mem_FP
    machineBoolDataBound_mem_FP

@[simp] theorem machineBoolDataRemaining_pack (remaining acc) :
    machineBoolDataRemaining (machineBoolDataPack remaining acc) =
      remaining := by
  simp [machineBoolDataRemaining, machineBoolDataPack]

@[simp] theorem machineBoolDataAcc_pack (remaining acc) :
    machineBoolDataAcc (machineBoolDataPack remaining acc) = acc := by
  simp [machineBoolDataAcc, machineBoolDataPack]

def MachineBoolDataStateBound
    (word : List Bool) (iterations : ℕ) (state : List Bool) : Prop :=
  state = machineBoolDataPack
      (machineBoolDataRemaining state) (machineBoolDataAcc state) ∧
    (machineBoolDataRemaining state).length ≤ word.length ∧
    (machineBoolDataAcc state).length ≤ 4 * iterations

theorem machineBoolDataInit_bound (word : List Bool) :
    MachineBoolDataStateBound word 0 (machineBoolDataInit word) := by
  simp [MachineBoolDataStateBound, machineBoolDataInit]

theorem machineBoolDataStep_bound
    {word state : List Bool} {iterations : ℕ}
    (hstate : MachineBoolDataStateBound word iterations state) :
    MachineBoolDataStateBound word (iterations + 1)
      (machineBoolDataStep state) := by
  rcases hstate with ⟨hdecomp, hremaining, hacc⟩
  cases hrem : machineBoolDataRemaining state with
  | nil =>
      rw [machineBoolDataStep, hrem, machineIfEmpty_nil]
      exact ⟨hdecomp, hremaining, hacc.trans (by omega)⟩
  | cons bit tail =>
      rw [machineBoolDataStep, hrem, machineIfEmpty_cons,
        machineBoolDataContinue]
      simp only [MachineBoolDataStateBound,
        machineBoolDataRemaining_pack, machineBoolDataAcc_pack,
        List.length_append, List.length_tail]
      refine ⟨trivial, ?_, ?_⟩
      · omega
      · have hbit : (machineBoolDataBitRuler state).length ≤ 4 := by
          rw [machineBoolDataBitRuler, hrem]
          cases bit <;> simp
        omega

theorem machineBoolDataIterate_bound (word : List Bool) : ∀ k,
    MachineBoolDataStateBound word k
      ((machineBoolDataStep)^[k] (machineBoolDataInit word)) := by
  intro k
  induction k with
  | zero => exact machineBoolDataInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineBoolDataStep_bound ih

theorem machineBoolDataIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ word.length) :
    ((machineBoolDataStep)^[iterations]
      (machineBoolDataInit word)).length ≤
        (machineBoolDataWidth word).length := by
  rcases machineBoolDataIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc⟩
  rw [hdecomp]
  simp only [machineBoolDataPack, machineBoolDataWidth, pair_length,
    machineBoolDataBound, List.length_append, List.length_replicate]
  omega

theorem machineBoolDataFinalState_mem_FP :
    machineBoolDataFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineBoolDataStep_mem_FP
    machineBoolDataInit_mem_FP id_mem_FP machineBoolDataWidth_mem_FP
    machineBoolDataIterate_length_le_width

theorem machineBoolDataLengthRuler_mem_FP :
    machineBoolDataLengthRuler ∈ Complexity.FP := by
  simpa only [machineBoolDataLengthRuler] using!
    machineCompose_mem_FP machineBoolDataFinalState_mem_FP
      machineBoolDataAcc_mem_FP

theorem machineBoolDataIterate_complete (word acc : List Bool) :
    (machineBoolDataStep)^[word.length]
        (machineBoolDataPack word acc) =
      machineBoolDataPack [] (acc ++ boolDataRuler word) := by
  induction word generalizing acc with
  | nil => simp [boolDataRuler]
  | cons bit word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [machineBoolDataStep, machineBoolDataRemaining_pack,
        machineIfEmpty_cons, machineBoolDataContinue,
        machineBoolDataAcc_pack, List.tail_cons]
      have hbit : machineBoolDataBitRuler
          (machineBoolDataPack (bit :: word) acc) =
          List.replicate (boolDataSize bit) true := by
        cases bit <;> simp [machineBoolDataBitRuler, boolDataSize]
      rw [hbit, ih]
      simp [boolDataRuler, List.append_assoc]

@[simp] theorem machineBoolDataLengthRuler_encode (word : List Bool) :
    machineBoolDataLengthRuler word = boolDataRuler word := by
  rw [machineBoolDataLengthRuler, machineBoolDataFinalState,
    machineBoolDataInit, machineBoolDataIterate_complete]
  simp

/-! ## One rational entry -/

def machineOptimizerEntryNumeratorCode (word : List Bool) : List Bool :=
  machineRationalEntryNumeratorWord word

def machineOptimizerEntryNatAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machineOptimizerEntryNumeratorCode word)

def machineOptimizerEntrySignRuler (word : List Bool) : List Bool :=
  machineIfHead (machineOptimizerEntryNumeratorCode word)
    (List.replicate 4 true) (List.replicate 2 true)

def machineOptimizerEntryNumeratorRuler (word : List Bool) : List Bool :=
  machineBoolDataLengthRuler (machineOptimizerEntryNatAbsBits word)

def machineOptimizerEntryDenominatorRuler (word : List Bool) : List Bool :=
  machineBoolDataLengthRuler
    (machineRationalEntryDenominatorWord word)

/-- A unary word of length exactly `encodedBitLength ℚ q` on a canonical
rational-entry input. -/
def machineOptimizerEntryLengthRuler (word : List Bool) : List Bool :=
  List.replicate 8 true ++
    (machineOptimizerEntrySignRuler word ++
      (machineOptimizerEntryNumeratorRuler word ++
        machineOptimizerEntryDenominatorRuler word))

theorem machineOptimizerEntryNumeratorCode_mem_FP :
    machineOptimizerEntryNumeratorCode ∈ Complexity.FP :=
  machineRationalEntryNumeratorWord_mem_FP

theorem machineOptimizerEntryNatAbsBits_mem_FP :
    machineOptimizerEntryNatAbsBits ∈ Complexity.FP := by
  simpa only [machineOptimizerEntryNatAbsBits] using!
    machineCompose_mem_FP machineOptimizerEntryNumeratorCode_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineOptimizerEntrySignRuler_mem_FP :
    machineOptimizerEntrySignRuler ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineOptimizerEntryNumeratorCode_mem_FP
    (machineConst_mem_FP (List.replicate 4 true))
    (machineConst_mem_FP (List.replicate 2 true))

theorem machineOptimizerEntryNumeratorRuler_mem_FP :
    machineOptimizerEntryNumeratorRuler ∈ Complexity.FP := by
  simpa only [machineOptimizerEntryNumeratorRuler] using!
    machineCompose_mem_FP machineOptimizerEntryNatAbsBits_mem_FP
      machineBoolDataLengthRuler_mem_FP

theorem machineOptimizerEntryDenominatorRuler_mem_FP :
    machineOptimizerEntryDenominatorRuler ∈ Complexity.FP := by
  simpa only [machineOptimizerEntryDenominatorRuler] using!
    machineCompose_mem_FP machineRationalEntryDenominatorWord_mem_FP
      machineBoolDataLengthRuler_mem_FP

theorem machineOptimizerEntryLengthRuler_mem_FP :
    machineOptimizerEntryLengthRuler ∈ Complexity.FP := by
  have htail := machineAppend_mem_FP
    machineOptimizerEntryNumeratorRuler_mem_FP
    machineOptimizerEntryDenominatorRuler_mem_FP
  have hpayload := machineAppend_mem_FP
    machineOptimizerEntrySignRuler_mem_FP htail
  simpa only [machineOptimizerEntryLengthRuler] using!
    machineAppend_mem_FP
      (machineConst_mem_FP (List.replicate 8 true)) hpayload

@[simp] theorem machineOptimizerEntryNumeratorCode_encode (q : ℚ) :
    machineOptimizerEntryNumeratorCode (rationalEntryBinaryCode q) =
      integerBinaryCode q.num := by
  exact machineRationalEntryNumeratorWord_encode q

@[simp] theorem machineOptimizerEntryNatAbsBits_encode (q : ℚ) :
    machineOptimizerEntryNatAbsBits (rationalEntryBinaryCode q) =
      q.num.natAbs.bits := by
  rw [machineOptimizerEntryNatAbsBits,
    machineOptimizerEntryNumeratorCode_encode,
    machineIntegerNatAbsBits_encode]

@[simp] theorem machineOptimizerEntrySignRuler_encode (q : ℚ) :
    machineOptimizerEntrySignRuler (rationalEntryBinaryCode q) =
      List.replicate (boolDataSize (integerPayload q.num).1) true := by
  rw [machineOptimizerEntrySignRuler,
    machineOptimizerEntryNumeratorCode_encode]
  cases q.num <;> simp [integerBinaryCode, integerPayload, boolDataSize]

@[simp] theorem machineOptimizerEntryNumeratorRuler_encode (q : ℚ) :
    machineOptimizerEntryNumeratorRuler (rationalEntryBinaryCode q) =
      boolDataRuler q.num.natAbs.bits := by
  simp [machineOptimizerEntryNumeratorRuler]

@[simp] theorem machineOptimizerEntryDenominatorRuler_encode (q : ℚ) :
    machineOptimizerEntryDenominatorRuler (rationalEntryBinaryCode q) =
      boolDataRuler q.den.bits := by
  simp [machineOptimizerEntryDenominatorRuler]

@[simp] theorem machineOptimizerEntryLengthRuler_encode (q : ℚ) :
    machineOptimizerEntryLengthRuler (rationalEntryBinaryCode q) =
      List.replicate (encodedBitLength ℚ q) true := by
  rw [machineOptimizerEntryLengthRuler,
    machineOptimizerEntrySignRuler_encode,
    machineOptimizerEntryNumeratorRuler_encode,
    machineOptimizerEntryDenominatorRuler_encode,
    rational_encodedBitLength_eq_boolDataLength]
  rw [boolDataRuler_eq_replicate, boolDataRuler_eq_replicate]
  simp only [← List.replicate_add]
  congr 1
  omega

end BeyondBethe
