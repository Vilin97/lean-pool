/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerSignedMagnitude

/-!
# Polynomial-time normalization of unreduced rationals

An unreduced signed fraction is encoded as the pair of its
`integerBinaryCode` numerator and ordinary denominator bits.  The machine
computes the absolute numerator, their gcd, both exact quotients, restores the
integer sign, and finally applies the public rational encoder.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def rawRatBinaryCode (q : RawRat) : List Bool :=
  pair (integerBinaryCode q.num) q.den.bits

def machineRawRatNatAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machinePairFirst word)

def machineRawRatGcdBits (word : List Bool) : List Bool :=
  machineBinaryGcdBits
    (pair (machineRawRatNatAbsBits word) (machinePairSecond word))

def machineRawRatAbsQuotientBits (word : List Bool) : List Bool :=
  machinePairFirst
    (machineBinaryDivModBits
      (pair (machineRawRatNatAbsBits word) (machineRawRatGcdBits word)))

def machineRawRatDenQuotientBits (word : List Bool) : List Bool :=
  machinePairFirst
    (machineBinaryDivModBits
      (pair (machinePairSecond word) (machineRawRatGcdBits word)))

def machineNormalizeRawRatEntryCode (word : List Bool) : List Bool :=
  pair
    (machineIntegerCodeFromSignedAbs
      (pair (machinePairFirst word) (machineRawRatAbsQuotientBits word)))
    (machineRawRatDenQuotientBits word)

/-- Public canonical rational output bits. -/
def machineNormalizeRawRatBinaryCode (word : List Bool) : List Bool :=
  machineRationalBinaryCode (machineNormalizeRawRatEntryCode word)

theorem machineRawRatNatAbsBits_mem_FP :
    machineRawRatNatAbsBits ∈ Complexity.FP := by
  simpa only [machineRawRatNatAbsBits] using!
    machineCompose_mem_FP machinePairFirst_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineRawRatGcdBits_mem_FP :
    machineRawRatGcdBits ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineRawRatNatAbsBits word)
      (machinePairSecond word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineRawRatNatAbsBits_mem_FP
      machinePairSecond_mem_FP
  simpa only [machineRawRatGcdBits] using!
    machineCompose_mem_FP hpair machineBinaryGcdBits_mem_FP

theorem machineRawRatAbsQuotientBits_mem_FP :
    machineRawRatAbsQuotientBits ∈ Complexity.FP := by
  have hpair : (fun word => pair (machineRawRatNatAbsBits word)
      (machineRawRatGcdBits word)) ∈ Complexity.FP :=
    machinePair_mem_FP machineRawRatNatAbsBits_mem_FP
      machineRawRatGcdBits_mem_FP
  have hdiv := machineCompose_mem_FP hpair machineBinaryDivModBits_mem_FP
  simpa only [machineRawRatAbsQuotientBits] using!
    machineCompose_mem_FP hdiv machinePairFirst_mem_FP

theorem machineRawRatDenQuotientBits_mem_FP :
    machineRawRatDenQuotientBits ∈ Complexity.FP := by
  have hpair : (fun word => pair (machinePairSecond word)
      (machineRawRatGcdBits word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairSecond_mem_FP machineRawRatGcdBits_mem_FP
  have hdiv := machineCompose_mem_FP hpair machineBinaryDivModBits_mem_FP
  simpa only [machineRawRatDenQuotientBits] using!
    machineCompose_mem_FP hdiv machinePairFirst_mem_FP

theorem machineNormalizeRawRatEntryCode_mem_FP :
    machineNormalizeRawRatEntryCode ∈ Complexity.FP := by
  have hsignedPair : (fun word => pair (machinePairFirst word)
      (machineRawRatAbsQuotientBits word)) ∈ Complexity.FP :=
    machinePair_mem_FP machinePairFirst_mem_FP
      machineRawRatAbsQuotientBits_mem_FP
  have hsigned := machineCompose_mem_FP hsignedPair
    machineIntegerCodeFromSignedAbs_mem_FP
  simpa only [machineNormalizeRawRatEntryCode] using!
    machinePair_mem_FP hsigned machineRawRatDenQuotientBits_mem_FP

theorem machineNormalizeRawRatBinaryCode_mem_FP :
    machineNormalizeRawRatBinaryCode ∈ Complexity.FP := by
  simpa only [machineNormalizeRawRatBinaryCode] using!
    machineCompose_mem_FP machineNormalizeRawRatEntryCode_mem_FP
      machineRationalBinaryCode_mem_FP

theorem machineRawRatNatAbsBits_encode (q : RawRat) :
    machineRawRatNatAbsBits (rawRatBinaryCode q) = q.num.natAbs.bits := by
  simp [machineRawRatNatAbsBits, rawRatBinaryCode,
    machineIntegerNatAbsBits_encode]

theorem machineRawRatGcdBits_encode (q : RawRat) :
    machineRawRatGcdBits (rawRatBinaryCode q) =
      (Nat.gcd q.num.natAbs q.den).bits := by
  rw [machineRawRatGcdBits, machineRawRatNatAbsBits_encode]
  simp only [rawRatBinaryCode, machinePairSecond_pair]
  rw [machineBinaryGcdBits_pair_natBits]

theorem machineRawRatAbsQuotientBits_encode (q : RawRat) :
    machineRawRatAbsQuotientBits (rawRatBinaryCode q) =
      (q.num.natAbs / Nat.gcd q.num.natAbs q.den).bits := by
  rw [machineRawRatAbsQuotientBits]
  rw [machineRawRatNatAbsBits_encode, machineRawRatGcdBits_encode,
    machineBinaryDivModBits_pair_natBits]
  simp only [machinePairFirst_pair]

theorem machineRawRatDenQuotientBits_encode (q : RawRat) :
    machineRawRatDenQuotientBits (rawRatBinaryCode q) =
      (q.den / Nat.gcd q.num.natAbs q.den).bits := by
  rw [machineRawRatDenQuotientBits]
  simp only [rawRatBinaryCode, machinePairSecond_pair]
  have hg : machineRawRatGcdBits
      (pair (integerBinaryCode q.num) q.den.bits) =
      (Nat.gcd q.num.natAbs q.den).bits := by
    simpa only [rawRatBinaryCode] using! machineRawRatGcdBits_encode q
  rw [hg, machineBinaryDivModBits_pair_natBits]
  simp only [machinePairFirst_pair]

theorem machineNormalizeRawRatEntryCode_encode (q : RawRat) :
    machineNormalizeRawRatEntryCode (rawRatBinaryCode q) =
      rationalEntryBinaryCode (binaryNormalizeRawRat q) := by
  let g := Nat.gcd q.num.natAbs q.den
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ q.den_pos
  have hgdvd : g ∣ q.num.natAbs := Nat.gcd_dvd_left _ _
  have hnum := machineIntegerCodeFromSignedAbs_div q.num g hgpos hgdvd
  have hden : (binaryLongDiv q.den g).1 = q.den / g := by
    simp [binaryLongDiv_eq_div_mod]
  rw [machineNormalizeRawRatEntryCode]
  simp only [rawRatBinaryCode, machinePairFirst_pair]
  have habs : machineRawRatAbsQuotientBits
      (pair (integerBinaryCode q.num) q.den.bits) =
      (q.num.natAbs / Nat.gcd q.num.natAbs q.den).bits := by
    simpa only [rawRatBinaryCode] using!
      machineRawRatAbsQuotientBits_encode q
  have hdenq : machineRawRatDenQuotientBits
      (pair (integerBinaryCode q.num) q.den.bits) =
      (q.den / Nat.gcd q.num.natAbs q.den).bits := by
    simpa only [rawRatBinaryCode] using!
      machineRawRatDenQuotientBits_encode q
  rw [habs, hdenq]
  change pair
      (machineIntegerCodeFromSignedAbs
        (pair (integerBinaryCode q.num) (q.num.natAbs / g).bits))
      (q.den / g).bits = _
  rw [hnum]
  rw [← hden]
  simp only [rationalEntryBinaryCode, binaryNormalizeRawRat]
  rw [binaryEuclidBounded_eq_gcd]

theorem machineNormalizeRawRatBinaryCode_encode (q : RawRat) :
    machineNormalizeRawRatBinaryCode (rawRatBinaryCode q) =
      rationalBinaryCode (binaryNormalizeRawRat q) := by
  rw [machineNormalizeRawRatBinaryCode,
    machineNormalizeRawRatEntryCode_encode,
    machineRationalBinaryCode_encode]

end BeyondBethe
