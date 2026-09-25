/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryCompare
public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryMul

/-!
# Polynomial-time canonical output encodings

The public rational output is the canonical bit expansion of a natural pairing
of the signed numerator code and positive denominator.  This file realizes
that pairing formula from the verified arithmetic primitives, and then proves
the complete rational encoder correct.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Squares the left binary natural-number component of a pair. -/
def machineNatPairLeftSquare (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machinePairFirst word) (machinePairFirst word))

/-- Squares the right binary natural-number component of a pair. -/
def machineNatPairRightSquare (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machinePairSecond word) (machinePairSecond word))

/-- Computes the natural-pairing branch `right^2 + left` in binary. -/
def machineNatPairLeftBranch (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineNatPairRightSquare word) (machinePairFirst word))

/-- Computes the intermediate natural-pairing term `left^2 + left` in binary. -/
def machineNatPairRightBranchFirst (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineNatPairLeftSquare word) (machinePairFirst word))

/-- Computes the natural-pairing branch `left^2 + left + right` in binary. -/
def machineNatPairRightBranch (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineNatPairRightBranchFirst word) (machinePairSecond word))

/-- Canonical bits of Mathlib's monotone natural pairing function. -/
def machineNatPairBits (word : List Bool) : List Bool :=
  machineIfHead (machineBinaryNatLtBit word)
    (machineNatPairLeftBranch word) (machineNatPairRightBranch word)

theorem machineNatPairLeftSquare_mem_FP :
    machineNatPairLeftSquare ∈ Complexity.FP := by
  have hpair : (fun word => pair (machinePairFirst word)
      (machinePairFirst word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairFirst_mem_FP machinePairFirst_mem_FP
  simpa only [machineNatPairLeftSquare] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineNatPairRightSquare_mem_FP :
    machineNatPairRightSquare ∈ Complexity.FP := by
  have hpair : (fun word => pair (machinePairSecond word)
      (machinePairSecond word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineNatPairRightSquare] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineNatPairLeftBranch_mem_FP :
    machineNatPairLeftBranch ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineNatPairRightSquare word)
      (machinePairFirst word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineNatPairRightSquare_mem_FP
      machinePairFirst_mem_FP
  simpa only [machineNatPairLeftBranch] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineNatPairRightBranchFirst_mem_FP :
    machineNatPairRightBranchFirst ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineNatPairLeftSquare word)
      (machinePairFirst word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineNatPairLeftSquare_mem_FP
      machinePairFirst_mem_FP
  simpa only [machineNatPairRightBranchFirst] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineNatPairRightBranch_mem_FP :
    machineNatPairRightBranch ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineNatPairRightBranchFirst word)
      (machinePairSecond word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineNatPairRightBranchFirst_mem_FP
      machinePairSecond_mem_FP
  simpa only [machineNatPairRightBranch] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineNatPairBits_mem_FP :
    machineNatPairBits ∈ Complexity.FP := by
  simpa only [machineNatPairBits] using!
    machineIfHead_mem_FP machineBinaryNatLtBit_mem_FP
      machineNatPairLeftBranch_mem_FP machineNatPairRightBranch_mem_FP

theorem machineNatPairBits_pair_natBits (a b : ℕ) :
    machineNatPairBits (pair a.bits b.bits) = (Nat.pair a b).bits := by
  simp only [machineNatPairBits, machineBinaryNatLtBit_pair_natBits]
  by_cases h : a < b
  · simp only [h, decide_true, machineIfHead_true,
      machineNatPairLeftBranch, machineNatPairRightSquare,
      machinePairFirst_pair, machinePairSecond_pair,
      machineBinaryMulBits_pair_natBits,
      machineBinaryAddBits_pair_natBits]
    simp [Nat.pair, h]
  · simp only [h, decide_false, machineIfHead_false,
      machineNatPairRightBranch, machineNatPairRightBranchFirst,
      machineNatPairLeftSquare, machinePairFirst_pair,
      machinePairSecond_pair, machineBinaryMulBits_pair_natBits,
      machineBinaryAddBits_pair_natBits]
    simp [Nat.pair, h, Nat.add_assoc]

/-- Drops the sign bit to expose the integer code's magnitude payload. -/
def machineIntegerMagnitudeWord (word : List Bool) : List Bool := word.tail

/-- Doubles the integer payload in binary to obtain its even natural-number code. -/
def machineIntegerEvenCodeBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineIntegerMagnitudeWord word)
      (machineIntegerMagnitudeWord word))

/-- Adds one to the doubled integer payload to obtain its odd natural-number code. -/
def machineIntegerOddCodeBits (word : List Bool) : List Bool :=
  machineBinaryAddBits (pair (machineIntegerEvenCodeBits word) [true])

/-- Convert the sign-and-magnitude `integerBinaryCode` to the natural code
used by the public rational output. -/
def machineIntegerNatCodeBits (word : List Bool) : List Bool :=
  machineIfHead word (machineIntegerOddCodeBits word)
    (machineIntegerEvenCodeBits word)

theorem machineIntegerMagnitudeWord_mem_FP :
    machineIntegerMagnitudeWord ∈ Complexity.FP := by
  simpa only [machineIntegerMagnitudeWord] using! machineTail_mem_FP

theorem machineIntegerEvenCodeBits_mem_FP :
    machineIntegerEvenCodeBits ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineIntegerMagnitudeWord word)
      (machineIntegerMagnitudeWord word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineIntegerMagnitudeWord_mem_FP
      machineIntegerMagnitudeWord_mem_FP
  simpa only [machineIntegerEvenCodeBits] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineIntegerOddCodeBits_mem_FP :
    machineIntegerOddCodeBits ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineIntegerEvenCodeBits word) [true]) ∈
      Complexity.FP :=
    machinePair_mem_FP machineIntegerEvenCodeBits_mem_FP
      (machineConst_mem_FP [true])
  simpa only [machineIntegerOddCodeBits] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineIntegerNatCodeBits_mem_FP :
    machineIntegerNatCodeBits ∈ Complexity.FP := by
  simpa only [machineIntegerNatCodeBits] using!
    machineIfHead_mem_FP id_mem_FP machineIntegerOddCodeBits_mem_FP
      machineIntegerEvenCodeBits_mem_FP

theorem machineIntegerNatCodeBits_encode (z : ℤ) :
    machineIntegerNatCodeBits (integerBinaryCode z) =
      (integerNatCode z).bits := by
  cases z with
  | ofNat n =>
      simp [machineIntegerNatCodeBits, integerBinaryCode,
        machineIntegerEvenCodeBits, machineIntegerMagnitudeWord,
        integerNatCode, machineBinaryAddBits_pair_natBits,
        two_mul]
  | negSucc n =>
      simp [machineIntegerNatCodeBits, integerBinaryCode,
        machineIntegerOddCodeBits, machineIntegerEvenCodeBits,
        machineIntegerMagnitudeWord, integerNatCode,
        machineBinaryAddBits_pair_natBits, two_mul]
      rw [show ([true] : List Bool) = (1 : ℕ).bits by rfl,
        machineBinaryAddBits_pair_natBits]

/-- Complete public rational output encoder, from the entry representation
used inside the matrix input to canonical `rationalBinaryCode`. -/
def machineRationalBinaryCode (word : List Bool) : List Bool :=
  machineNatPairBits
    (pair
      (machineIntegerNatCodeBits
        (machineRationalEntryNumeratorWord word))
      (machineRationalEntryDenominatorWord word))

theorem machineRationalBinaryCode_mem_FP :
    machineRationalBinaryCode ∈ Complexity.FP := by
  have hnum : (fun word => machineIntegerNatCodeBits
      (machineRationalEntryNumeratorWord word)) ∈ Complexity.FP :=
    machineCompose_mem_FP machineRationalEntryNumeratorWord_mem_FP
      machineIntegerNatCodeBits_mem_FP
  have hpair : (fun word => pair
      (machineIntegerNatCodeBits
        (machineRationalEntryNumeratorWord word))
      (machineRationalEntryDenominatorWord word)) ∈ Complexity.FP :=
    machinePair_mem_FP hnum machineRationalEntryDenominatorWord_mem_FP
  simpa only [machineRationalBinaryCode] using!
    machineCompose_mem_FP hpair machineNatPairBits_mem_FP

theorem machineRationalBinaryCode_encode (q : ℚ) :
    machineRationalBinaryCode (rationalEntryBinaryCode q) =
      rationalBinaryCode q := by
  simp only [machineRationalBinaryCode,
    machineRationalEntryNumeratorWord_encode,
    machineRationalEntryDenominatorWord_encode,
    machineIntegerNatCodeBits_encode,
    machineNatPairBits_pair_natBits]
  rfl

end BeyondBethe
