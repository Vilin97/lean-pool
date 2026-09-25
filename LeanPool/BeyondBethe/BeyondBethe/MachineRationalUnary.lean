/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalArithmetic
public import LeanPool.BeyondBethe.BeyondBethe.RawRationalBitBounds

/-!
# Polynomial-time rational negation, inversion, and division

The reciprocal machine handles zero explicitly and otherwise swaps the
positive denominator with the absolute numerator while preserving the
numerator sign.  Division is multiplication by this verified reciprocal.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Negates a raw rational's signed numerator while preserving its denominator. -/
def machineRawRatNegCode (word : List Bool) : List Bool :=
  pair (machineIntegerNegCode (machinePairFirst word))
    (machinePairSecond word)

/-- Encodes the reciprocal of a nonzero raw rational using its old denominator with the original
numerator sign as the new numerator, and the old numerator magnitude as the new denominator. -/
def machineRawRatInvNonzeroCode (word : List Bool) : List Bool :=
  pair
    (machineCanonicalIntegerFromSignedAbs
      (pair (machineHeadBit (machinePairFirst word))
        (machinePairSecond word)))
    (machineIntegerNatAbsBits (machinePairFirst word))

/-- Returns canonical raw zero for a zero numerator and the signed reciprocal code otherwise. -/
def machineRawRatInvCode (word : List Bool) : List Bool :=
  machineIfEmpty (machineIntegerNatAbsBits (machinePairFirst word))
    (pair [false] [true]) (machineRawRatInvNonzeroCode word)

/-- Multiplies the left raw rational by the totalized reciprocal of the right. -/
def machineRawRatDivCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machinePairFirst word)
      (machineRawRatInvCode (machinePairSecond word)))

/-- Normalizes a raw negation into the rational binary output encoding. -/
def machineRationalNegCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatNegCode word)

/-- Normalizes a totalized raw reciprocal into the rational binary output encoding. -/
def machineRationalInvCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatInvCode word)

/-- Normalizes a raw quotient into the rational binary output encoding. -/
def machineRationalDivCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatDivCode word)

theorem machineRawRatNegCode_mem_FP : machineRawRatNegCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerNegCode_mem_FP
  exact machinePair_mem_FP hnum machinePairSecond_mem_FP

theorem machineRawRatInvNonzeroCode_mem_FP :
    machineRawRatInvNonzeroCode ∈ Complexity.FP := by
  have hsign := machineCompose_mem_FP machinePairFirst_mem_FP
    machineHeadBit_mem_FP
  have hsigned := machinePair_mem_FP hsign machinePairSecond_mem_FP
  have hnum := machineCompose_mem_FP hsigned
    machineCanonicalIntegerFromSignedAbs_mem_FP
  have habs := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerNatAbsBits_mem_FP
  exact machinePair_mem_FP hnum habs

theorem machineRawRatInvCode_mem_FP : machineRawRatInvCode ∈ Complexity.FP := by
  have habs := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerNatAbsBits_mem_FP
  exact machineIfEmpty_mem_FP habs
    (machineConst_mem_FP (pair [false] [true]))
    machineRawRatInvNonzeroCode_mem_FP

theorem machineRawRatDivCode_mem_FP : machineRawRatDivCode ∈ Complexity.FP := by
  have hinv := machineCompose_mem_FP machinePairSecond_mem_FP
    machineRawRatInvCode_mem_FP
  have hpair := machinePair_mem_FP machinePairFirst_mem_FP hinv
  simpa only [machineRawRatDivCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineRationalNegCode_mem_FP : machineRationalNegCode ∈ Complexity.FP := by
  simpa only [machineRationalNegCode] using!
    machineCompose_mem_FP machineRawRatNegCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineRationalInvCode_mem_FP : machineRationalInvCode ∈ Complexity.FP := by
  simpa only [machineRationalInvCode] using!
    machineCompose_mem_FP machineRawRatInvCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineRationalDivCode_mem_FP : machineRationalDivCode ∈ Complexity.FP := by
  simpa only [machineRationalDivCode] using!
    machineCompose_mem_FP machineRawRatDivCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineRawRatNegCode_encode (q : RawRat) :
    machineRawRatNegCode (rawRatBinaryCode q) = rawRatBinaryCode q.neg := by
  simp [machineRawRatNegCode, rawRatBinaryCode,
    machineIntegerNegCode_encode, RawRat.neg]

theorem machineRawRatInvNonzeroCode_encode (q : RawRat) (hq : q.num ≠ 0) :
    machineRawRatInvNonzeroCode (rawRatBinaryCode q) =
      rawRatBinaryCode q.inv := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      cases n with
      | zero => contradiction
      | succ n =>
          simp only [machineRawRatInvNonzeroCode, rawRatBinaryCode,
            machinePairFirst_pair, machinePairSecond_pair,
            machineHeadBit_cons, machineIntegerNatAbsBits_encode,
            RawRat.inv]
          change pair
            (machineCanonicalIntegerFromSignedAbs (pair [false] den.bits))
            (n + 1).bits = pair (integerBinaryCode (den : ℤ)) (n + 1).bits
          rw [machineCanonicalIntegerFromSignedAbs_pair]
          rfl
  | negSucc n =>
      simp only [machineRawRatInvNonzeroCode, rawRatBinaryCode,
        machinePairFirst_pair, machinePairSecond_pair,
        machineHeadBit_cons, machineIntegerNatAbsBits_encode,
        RawRat.inv]
      change pair
        (machineCanonicalIntegerFromSignedAbs (pair [true] den.bits))
        (n + 1).bits = pair (integerBinaryCode (-(den : ℤ))) (n + 1).bits
      rw [machineCanonicalIntegerFromSignedAbs_pair]
      simp [signedMagnitudeValue]

theorem machineRawRatInvCode_encode (q : RawRat) :
    machineRawRatInvCode (rawRatBinaryCode q) = rawRatBinaryCode q.inv := by
  by_cases hq : q.num = 0
  · have habs : q.num.natAbs.bits = [] := by simp [hq]
    rw [machineRawRatInvCode]
    simp only [rawRatBinaryCode, machinePairFirst_pair,
      machineIntegerNatAbsBits_encode, habs, machineIfEmpty_nil]
    simp [RawRat.inv, RawRat.zero, hq, rawRatBinaryCode,
      integerBinaryCode]
  · have habs : q.num.natAbs.bits ≠ [] :=
      natBits_ne_nil_of_ne_zero (Int.natAbs_ne_zero.mpr hq)
    rw [machineRawRatInvCode]
    simp only [rawRatBinaryCode, machinePairFirst_pair,
      machineIntegerNatAbsBits_encode]
    rw [machineIfEmpty_of_ne_nil q.num.natAbs.bits
      (pair [false] [true])
      (machineRawRatInvNonzeroCode
        (pair (integerBinaryCode q.num) q.den.bits)) habs]
    simpa only [rawRatBinaryCode] using!
      machineRawRatInvNonzeroCode_encode q hq

theorem machineRawRatDivCode_encode (q r : RawRat) :
    machineRawRatDivCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rawRatBinaryCode (q.div r) := by
  rw [machineRawRatDivCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineRawRatInvCode_encode, machineRawRatMulCode_encode, RawRat.div]

theorem machineRationalNegCode_encode (q : RawRat) :
    machineRationalNegCode (rawRatBinaryCode q) =
      rationalBinaryCode (binaryNormalizeRawRat q.neg) := by
  rw [machineRationalNegCode, machineRawRatNegCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

theorem machineRationalInvCode_encode (q : RawRat) :
    machineRationalInvCode (rawRatBinaryCode q) =
      rationalBinaryCode (binaryNormalizeRawRat q.inv) := by
  rw [machineRationalInvCode, machineRawRatInvCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

theorem machineRationalDivCode_encode (q r : RawRat) :
    machineRationalDivCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rationalBinaryCode (binaryNormalizeRawRat (q.div r)) := by
  rw [machineRationalDivCode, machineRawRatDivCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

end BeyondBethe
