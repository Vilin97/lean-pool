/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateScales
import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerSignedMagnitude

/-!
# The input-dependent directed-logarithm schedule

`scheduledLogLower q p` uses `directedLogTerms q p`, not merely `p`, series
terms.  This module computes that exact term count from the unary precision
ruler and the signed dyadic exponent of `q`, expands it under a quadratic
guard, and invokes the verified directed-logarithm machine.
-/

namespace BeyondBethe

open Complexity

def machineScheduledLogPrecisionRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineScheduledLogArgumentRawCode (word : List Bool) : List Bool :=
  machinePairSecond word

def machineScheduledLogPrecisionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineScheduledLogPrecisionRuler word)

def machineScheduledLogExponentIntegerCode (word : List Bool) : List Bool :=
  machineDirectedLogExponentIntegerCode word

def machineScheduledLogExponentAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits
    (machineScheduledLogExponentIntegerCode word)

def machineScheduledLogPrecisionPlusExponentBits
    (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineScheduledLogPrecisionBits word)
      (machineScheduledLogExponentAbsBits word))

def machineScheduledLogTermsBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineScheduledLogPrecisionPlusExponentBits word)
      (2 : ℕ).bits)

/-- A total quadratic guard.  On canonical inputs it dominates the exact
input-dependent term count. -/
def machineScheduledLogTermsGuard (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineScheduledLogTermsRuler (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineScheduledLogTermsGuard word)
      (machineScheduledLogTermsBits word))

def machineScheduledLogLowerRawCode (word : List Bool) : List Bool :=
  machineDirectedLogLowerRawCode
    (pair (machineScheduledLogTermsRuler word)
      (machineScheduledLogArgumentRawCode word))

def machineScheduledLogUpperRawCode (word : List Bool) : List Bool :=
  machineDirectedLogUpperRawCode
    (pair (machineScheduledLogTermsRuler word)
      (machineScheduledLogArgumentRawCode word))

theorem machineScheduledLogPrecisionRuler_mem_FP :
    machineScheduledLogPrecisionRuler ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineScheduledLogArgumentRawCode_mem_FP :
    machineScheduledLogArgumentRawCode ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineScheduledLogPrecisionBits_mem_FP :
    machineScheduledLogPrecisionBits ∈ Complexity.FP := by
  simpa only [machineScheduledLogPrecisionBits] using!
    machineCompose_mem_FP machineScheduledLogPrecisionRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineScheduledLogExponentIntegerCode_mem_FP :
    machineScheduledLogExponentIntegerCode ∈ Complexity.FP := by
  simpa only [machineScheduledLogExponentIntegerCode] using!
    machineDirectedLogExponentIntegerCode_mem_FP

theorem machineScheduledLogExponentAbsBits_mem_FP :
    machineScheduledLogExponentAbsBits ∈ Complexity.FP := by
  simpa only [machineScheduledLogExponentAbsBits] using!
    machineCompose_mem_FP machineScheduledLogExponentIntegerCode_mem_FP
      machineIntegerNatAbsBits_mem_FP

theorem machineScheduledLogPrecisionPlusExponentBits_mem_FP :
    machineScheduledLogPrecisionPlusExponentBits ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineScheduledLogPrecisionBits_mem_FP
    machineScheduledLogExponentAbsBits_mem_FP
  simpa only [machineScheduledLogPrecisionPlusExponentBits] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineScheduledLogTermsBits_mem_FP :
    machineScheduledLogTermsBits ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineScheduledLogPrecisionPlusExponentBits_mem_FP
    (machineConst_mem_FP (2 : ℕ).bits)
  simpa only [machineScheduledLogTermsBits] using!
    machineCompose_mem_FP hpair machineBinaryAddBits_mem_FP

theorem machineScheduledLogTermsGuard_mem_FP :
    machineScheduledLogTermsGuard ∈ Complexity.FP :=
  machineBinaryMulWidth_mem_FP

theorem machineScheduledLogTermsRuler_mem_FP :
    machineScheduledLogTermsRuler ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineScheduledLogTermsGuard_mem_FP
    machineScheduledLogTermsBits_mem_FP
  simpa only [machineScheduledLogTermsRuler] using!
    machineCompose_mem_FP hpair machineBoundedUnary_mem_FP

theorem machineScheduledLogLowerRawCode_mem_FP :
    machineScheduledLogLowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineScheduledLogTermsRuler_mem_FP
    machineScheduledLogArgumentRawCode_mem_FP
  simpa only [machineScheduledLogLowerRawCode] using!
    machineCompose_mem_FP hpair machineDirectedLogLowerRawCode_mem_FP

theorem machineScheduledLogUpperRawCode_mem_FP :
    machineScheduledLogUpperRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineScheduledLogTermsRuler_mem_FP
    machineScheduledLogArgumentRawCode_mem_FP
  simpa only [machineScheduledLogUpperRawCode] using!
    machineCompose_mem_FP hpair machineDirectedLogUpperRawCode_mem_FP

@[simp] theorem machineScheduledLogPrecisionBits_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogPrecisionBits
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) = p.bits := by
  simp [machineScheduledLogPrecisionBits,
    machineScheduledLogPrecisionRuler]

@[simp] theorem machineScheduledLogExponentIntegerCode_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogExponentIntegerCode
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      integerBinaryCode (rationalBinaryExponent q) := by
  rw [machineScheduledLogExponentIntegerCode,
    machineDirectedLogExponentIntegerCode_encode,
    binaryRationalBinaryExponent_eq]

@[simp] theorem machineScheduledLogExponentAbsBits_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogExponentAbsBits
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      (rationalBinaryExponent q).natAbs.bits := by
  rw [machineScheduledLogExponentAbsBits,
    machineScheduledLogExponentIntegerCode_encode,
    machineIntegerNatAbsBits_encode]

@[simp] theorem machineScheduledLogTermsBits_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogTermsBits
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      (directedLogTerms q p).bits := by
  rw [machineScheduledLogTermsBits,
    machineScheduledLogPrecisionPlusExponentBits,
    machineScheduledLogPrecisionBits_encode,
    machineScheduledLogExponentAbsBits_encode,
    machineBinaryAddBits_pair_natBits]
  change machineBinaryAddBits
      (pair (p + (rationalBinaryExponent q).natAbs).bits (2 : ℕ).bits) = _
  rw [machineBinaryAddBits_pair_natBits]
  rfl

theorem rationalBinaryExponent_natAbs_le_two_rawWidth (q : ℚ) :
    (rationalBinaryExponent q).natAbs ≤
      2 * rawRatWidth (rawRatOfRat q) := by
  have habs := Int.natAbs_sub_le
    (Nat.log 2 q.num.natAbs : ℤ) (Nat.log 2 q.den : ℤ)
  simp only [Int.natAbs_natCast] at habs
  have hnum : Nat.log 2 q.num.natAbs ≤
      rawRatWidth (rawRatOfRat q) := by
    rw [← binaryNatLog2_eq_log_two, binaryNatLog2]
    exact (Nat.sub_le _ _).trans (le_max_left _ _)
  have hden : Nat.log 2 q.den ≤ rawRatWidth (rawRatOfRat q) := by
    rw [← binaryNatLog2_eq_log_two, binaryNatLog2]
    exact (Nat.sub_le _ _).trans (le_max_right _ _)
  rw [rationalBinaryExponent]
  omega

theorem directedLogTerms_le_scheduledLogGuard (q : ℚ) (p : ℕ) :
    directedLogTerms q p ≤
      (machineScheduledLogTermsGuard
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q)))).length := by
  let code := rawRatBinaryCode (rawRatOfRat q)
  let word := pair (List.replicate p true) code
  have hwidth := rawRatWidth_le_binaryCode_length (rawRatOfRat q)
  have hexp := rationalBinaryExponent_natAbs_le_two_rawWidth q
  have hword : word.length = 2 * p + code.length + 2 := by
    simp [word]
    omega
  have hterms : directedLogTerms q p ≤ 3 * word.length + 2 := by
    rw [directedLogTerms]
    simp only [word, code] at hword ⊢
    omega
  have hquad : 3 * word.length + 2 ≤ (word.length + 16) ^ 2 := by
    nlinarith [sq_nonneg (word.length + 14)]
  simpa only [machineScheduledLogTermsGuard, machineBinaryMulWidth,
    List.length_replicate, List.length_append, pow_two,
    List.length_cons, List.length_nil, Nat.zero_add, word, Nat.add_comm] using!
      hterms.trans hquad

@[simp] theorem machineScheduledLogTermsRuler_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogTermsRuler
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      List.replicate (directedLogTerms q p) true := by
  rw [machineScheduledLogTermsRuler,
    machineScheduledLogTermsBits_encode,
    machineBoundedUnary_encode_of_le]
  exact directedLogTerms_le_scheduledLogGuard q p

def rawScheduledLogLower (q : ℚ) (p : ℕ) : RawRat :=
  RawRat.logLower q (directedLogTerms q p)

def rawScheduledLogUpper (q : ℚ) (p : ℕ) : RawRat :=
  RawRat.logUpper q (directedLogTerms q p)

@[simp] theorem machineScheduledLogLowerRawCode_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogLowerRawCode
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (rawScheduledLogLower q p) := by
  rw [machineScheduledLogLowerRawCode,
    machineScheduledLogTermsRuler_encode]
  simp only [machineScheduledLogArgumentRawCode, machinePairSecond_pair,
    machineDirectedLogLowerRawCode_encode, rawScheduledLogLower]

@[simp] theorem machineScheduledLogUpperRawCode_encode
    (q : ℚ) (p : ℕ) :
    machineScheduledLogUpperRawCode
        (pair (List.replicate p true)
          (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (rawScheduledLogUpper q p) := by
  rw [machineScheduledLogUpperRawCode,
    machineScheduledLogTermsRuler_encode]
  simp only [machineScheduledLogArgumentRawCode, machinePairSecond_pair,
    machineDirectedLogUpperRawCode_encode, rawScheduledLogUpper]

theorem rawScheduledLogLower_value (q : ℚ) (p : ℕ) :
    (rawScheduledLogLower q p).value = scheduledLogLower q p := by
  simp [rawScheduledLogLower, scheduledLogLower,
    RawRat.value_logLower, binaryDirectedLogLower_eq]

theorem rawScheduledLogUpper_value (q : ℚ) (p : ℕ) :
    (rawScheduledLogUpper q p).value = scheduledLogUpper q p := by
  simp [rawScheduledLogUpper, scheduledLogUpper,
    RawRat.value_logUpper, binaryDirectedLogUpper_eq]

end BeyondBethe
