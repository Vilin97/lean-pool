/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBoundedUnary
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalLogSeries

/-!
# Guarded polynomial-time directed rational exponential

The mathematical exponential routine uses

`M = 2 * ceil (|s| + |s|^2 / loss) + 1`

and returns `(1 + s/M)^M`.  The binary code of `M` is always inexpensive to
compute, but a unary power ruler of length `M` is polynomial only on the
paper-specific domain where `M` has an a priori polynomial bound.  Accordingly
this machine takes an explicit unary guard.  It is polynomial-time on every
string and agrees exactly with the directed rational exponential whenever the
guard has length at least `M`.
-/

namespace BeyondBethe

open Complexity

def machineExpGuard (word : List Bool) : List Bool :=
  machinePairFirst word

def machineExpPayload (word : List Bool) : List Bool :=
  machinePairSecond word

def machineExpArgumentCode (word : List Bool) : List Bool :=
  machinePairFirst (machineExpPayload word)

def machineExpLossCode (word : List Bool) : List Bool :=
  machinePairSecond (machineExpPayload word)

def machineExpArgumentSign (word : List Bool) : List Bool :=
  machineHeadBit (machinePairFirst (machineExpArgumentCode word))

def machineExpMagnitudeCode (word : List Bool) : List Bool :=
  machineIfHead (machineExpArgumentSign word)
    (machineRawRatNegCode (machineExpArgumentCode word))
    (machineExpArgumentCode word)

def machineExpSquareCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineExpMagnitudeCode word) (machineExpMagnitudeCode word))

def machineExpSquareOverLossCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineExpSquareCode word) (machineExpLossCode word))

def machineExpScheduleArgumentCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineExpMagnitudeCode word)
      (machineExpSquareOverLossCode word))

def machineExpCeilBits (word : List Bool) : List Bool :=
  machineRationalCeilNatBits (machineExpScheduleArgumentCode word)

/-- Little-endian binary code of `2 * ceil(...) + 1`. -/
def machineExpStepsBits (word : List Bool) : List Bool :=
  true :: machineExpCeilBits word

def machineExpStepsRuler (word : List Bool) : List Bool :=
  machineBoundedUnary (pair (machineExpGuard word) (machineExpStepsBits word))

def machineExpStepsRawRatCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode (machineExpStepsBits word)) [true]

def machineExpScaledArgumentCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineExpArgumentCode word) (machineExpStepsRawRatCode word))

def machineExpBaseCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair rawRatOneCode (machineExpScaledArgumentCode word))

/-- Total guarded machine for the directed rational lower exponential. -/
def machineBoundedRationalExpLowerCode (word : List Bool) : List Bool :=
  machineRationalPowerCode
    (pair (machineExpStepsRuler word) (machineExpBaseCode word))

/-- Raw-entry variant used by certificate composition.  It avoids decoding the
public one-natural-number rational output before the next rational operation. -/
def machineBoundedRationalExpLowerRawPowerCode
    (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineExpStepsRuler word) (machineExpBaseCode word))

def machineBoundedRationalExpLowerRawEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineBoundedRationalExpLowerRawPowerCode word)

theorem machineExpGuard_mem_FP : machineExpGuard ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineExpPayload_mem_FP : machineExpPayload ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineExpArgumentCode_mem_FP :
    machineExpArgumentCode ∈ Complexity.FP := by
  simpa only [machineExpArgumentCode] using
    machineCompose_mem_FP machineExpPayload_mem_FP machinePairFirst_mem_FP

theorem machineExpLossCode_mem_FP : machineExpLossCode ∈ Complexity.FP := by
  simpa only [machineExpLossCode] using
    machineCompose_mem_FP machineExpPayload_mem_FP machinePairSecond_mem_FP

theorem machineExpArgumentSign_mem_FP :
    machineExpArgumentSign ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineExpArgumentCode_mem_FP
    machinePairFirst_mem_FP
  simpa only [machineExpArgumentSign] using
    machineCompose_mem_FP hnum machineHeadBit_mem_FP

theorem machineExpMagnitudeCode_mem_FP :
    machineExpMagnitudeCode ∈ Complexity.FP := by
  have hneg := machineCompose_mem_FP machineExpArgumentCode_mem_FP
    machineRawRatNegCode_mem_FP
  simpa only [machineExpMagnitudeCode] using
    machineIfHead_mem_FP machineExpArgumentSign_mem_FP hneg
      machineExpArgumentCode_mem_FP

theorem machineExpSquareCode_mem_FP : machineExpSquareCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpMagnitudeCode_mem_FP
    machineExpMagnitudeCode_mem_FP
  simpa only [machineExpSquareCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineExpSquareOverLossCode_mem_FP :
    machineExpSquareOverLossCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpSquareCode_mem_FP
    machineExpLossCode_mem_FP
  simpa only [machineExpSquareOverLossCode] using
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineExpScheduleArgumentCode_mem_FP :
    machineExpScheduleArgumentCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpMagnitudeCode_mem_FP
    machineExpSquareOverLossCode_mem_FP
  simpa only [machineExpScheduleArgumentCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineExpCeilBits_mem_FP : machineExpCeilBits ∈ Complexity.FP := by
  simpa only [machineExpCeilBits] using
    machineCompose_mem_FP machineExpScheduleArgumentCode_mem_FP
      machineRationalCeilNatBits_mem_FP

theorem machineExpStepsBits_mem_FP : machineExpStepsBits ∈ Complexity.FP := by
  simpa only [machineExpStepsBits] using
    machineCompose_mem_FP machineExpCeilBits_mem_FP
      (machinePrepend_mem_FP true)

theorem machineExpStepsRuler_mem_FP :
    machineExpStepsRuler ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpGuard_mem_FP
    machineExpStepsBits_mem_FP
  simpa only [machineExpStepsRuler] using
    machineCompose_mem_FP hpair machineBoundedUnary_mem_FP

theorem machineExpStepsRawRatCode_mem_FP :
    machineExpStepsRawRatCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineExpStepsBits_mem_FP
    (machinePrepend_mem_FP false)
  exact machinePair_mem_FP hnum (machineConst_mem_FP [true])

theorem machineExpScaledArgumentCode_mem_FP :
    machineExpScaledArgumentCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpArgumentCode_mem_FP
    machineExpStepsRawRatCode_mem_FP
  simpa only [machineExpScaledArgumentCode] using
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineExpBaseCode_mem_FP : machineExpBaseCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatOneCode)
    machineExpScaledArgumentCode_mem_FP
  simpa only [machineExpBaseCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineBoundedRationalExpLowerCode_mem_FP :
    machineBoundedRationalExpLowerCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpStepsRuler_mem_FP
    machineExpBaseCode_mem_FP
  simpa only [machineBoundedRationalExpLowerCode] using
    machineCompose_mem_FP hpair machineRationalPowerCode_mem_FP

theorem machineBoundedRationalExpLowerRawPowerCode_mem_FP :
    machineBoundedRationalExpLowerRawPowerCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineExpStepsRuler_mem_FP
    machineExpBaseCode_mem_FP
  simpa only [machineBoundedRationalExpLowerRawPowerCode] using
    machineCompose_mem_FP hpair machineRawRatPowerCode_mem_FP

theorem machineBoundedRationalExpLowerRawEntryCode_mem_FP :
    machineBoundedRationalExpLowerRawEntryCode ∈ Complexity.FP := by
  simpa only [machineBoundedRationalExpLowerRawEntryCode] using
    machineCompose_mem_FP
      machineBoundedRationalExpLowerRawPowerCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

/-! ## Exact semantics when the schedule fits the guard -/

namespace RawRat

/-- Magnitude used only to choose the exponential schedule. -/
def expMagnitude (q : RawRat) : RawRat :=
  match q.num with
  | .ofNat _ => q
  | .negSucc _ => q.neg

def expApproxSteps (s loss : RawRat) : ℕ :=
  binaryRationalExpApproxSteps (expMagnitude s).value loss.value

end RawRat

@[simp] theorem machineExpGuard_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpGuard
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      guard := by
  simp [machineExpGuard]

@[simp] theorem machineExpArgumentCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpArgumentCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode s := by
  simp [machineExpArgumentCode, machineExpPayload]

@[simp] theorem machineExpLossCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpLossCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode loss := by
  simp [machineExpLossCode, machineExpPayload]

@[simp] theorem machineExpMagnitudeCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpMagnitudeCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode (RawRat.expMagnitude s) := by
  rcases s with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      simp [machineExpMagnitudeCode, machineExpArgumentSign,
        machineExpArgumentCode, machineExpPayload, rawRatBinaryCode,
        integerBinaryCode, RawRat.expMagnitude]
  | negSucc n =>
      simp only [machineExpMagnitudeCode, machineExpArgumentSign,
        machineExpArgumentCode, machineExpPayload, rawRatBinaryCode,
        integerBinaryCode, machinePairSecond_pair, machinePairFirst_pair,
        machineHeadBit_cons, machineIfHead_true, RawRat.expMagnitude]
      simpa only [rawRatBinaryCode] using
        (machineRawRatNegCode_encode
          (⟨Int.negSucc n, den, hden⟩ : RawRat))

@[simp] theorem machineExpSquareCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpSquareCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode
        ((RawRat.expMagnitude s).mul (RawRat.expMagnitude s)) := by
  rw [machineExpSquareCode]
  simp only [machineExpMagnitudeCode_encode, machineRawRatMulCode_encode]

@[simp] theorem machineExpSquareOverLossCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpSquareOverLossCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode
        (((RawRat.expMagnitude s).mul (RawRat.expMagnitude s)).div loss) := by
  rw [machineExpSquareOverLossCode]
  simp only [machineExpSquareCode_encode, machineExpLossCode_encode,
    machineRawRatDivCode_encode]

@[simp] theorem machineExpScheduleArgumentCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpScheduleArgumentCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode
        ((RawRat.expMagnitude s).add
          (((RawRat.expMagnitude s).mul (RawRat.expMagnitude s)).div loss)) := by
  rw [machineExpScheduleArgumentCode]
  simp only [machineExpMagnitudeCode_encode,
    machineExpSquareOverLossCode_encode, machineRawRatAddCode_encode]

@[simp] theorem machineExpCeilBits_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpCeilBits
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      (Int.toNat (binaryRatCeil
        ((RawRat.expMagnitude s).value +
          (RawRat.expMagnitude s).value ^ 2 / loss.value))).bits := by
  rw [machineExpCeilBits, machineExpScheduleArgumentCode_encode,
    machineRationalCeilNatBits_encode]
  congr 2
  rw [RawRat.value_add, RawRat.value_div, RawRat.value_mul]
  ring

@[simp] theorem machineExpStepsBits_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpStepsBits
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      (RawRat.expApproxSteps s loss).bits := by
  rw [machineExpStepsBits, machineExpCeilBits_encode]
  simp [RawRat.expApproxSteps, binaryRationalExpApproxSteps,
    binaryRationalCeilNat, binaryRatAdd_eq_add,
    binaryRatDiv_eq_div, binaryRatPow_eq_pow]

@[simp] theorem machineExpStepsRawRatCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpStepsRawRatCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode (RawRat.ofNat (RawRat.expApproxSteps s loss)) := by
  rw [machineExpStepsRawRatCode, machineExpStepsBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [rawRatBinaryCode, RawRat.ofNat]

@[simp] theorem machineExpStepsRuler_encode
    (guard : List Bool) (s loss : RawRat)
    (hsteps : RawRat.expApproxSteps s loss ≤ guard.length) :
    machineExpStepsRuler
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      List.replicate (RawRat.expApproxSteps s loss) true := by
  rw [machineExpStepsRuler]
  simp only [machineExpGuard_encode, machineExpStepsBits_encode]
  exact machineBoundedUnary_encode_of_le guard _ hsteps

@[simp] theorem machineExpScaledArgumentCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpScaledArgumentCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode (s.div (RawRat.ofNat (RawRat.expApproxSteps s loss))) := by
  rw [machineExpScaledArgumentCode]
  simp only [machineExpArgumentCode_encode,
    machineExpStepsRawRatCode_encode, machineRawRatDivCode_encode]

@[simp] theorem machineExpBaseCode_encode
    (guard : List Bool) (s loss : RawRat) :
    machineExpBaseCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode
        (RawRat.one.add
          (s.div (RawRat.ofNat (RawRat.expApproxSteps s loss)))) := by
  rw [machineExpBaseCode]
  simp only [rawRatOneCode, machineExpScaledArgumentCode_encode,
    machineRawRatAddCode_encode]

theorem binaryNormalizeRawRat_expBasePow_eq
    (s loss : RawRat) :
    binaryNormalizeRawRat
        ((RawRat.one.add
          (s.div (RawRat.ofNat (RawRat.expApproxSteps s loss)))).pow
            (RawRat.expApproxSteps s loss)) =
      binaryRationalExpLower s.value loss.value := by
  rw [binaryNormalizeRawRat_eq_value, RawRat.value_pow,
    RawRat.value_add, RawRat.value_one, RawRat.value_div,
    RawRat.value_ofNat]
  rcases s with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      have hs : 0 ≤ ((⟨Int.ofNat n, den, hden⟩ : RawRat).value) := by
        change (0 : ℚ) ≤ (n : ℚ) / (den : ℚ)
        exact div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg den)
      rw [binaryRationalExpLower,
        if_pos ((binaryRatNonnegative_eq_true_iff _).2 hs),
        binaryRationalPositiveExpLower]
      simp [RawRat.expApproxSteps, RawRat.expMagnitude,
        binaryRatAdd_eq_add, binaryRatDiv_eq_div,
        binaryRatPow_eq_pow]
  | negSucc n =>
      have hs : ¬ 0 ≤ ((⟨Int.negSucc n, den, hden⟩ : RawRat).value) := by
        rw [RawRat.value]
        have hn : (0 : ℚ) ≤ n := by positivity
        have hnum : (((Int.negSucc n : ℤ) : ℚ)) < 0 := by
          norm_num only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
          linarith
        have hdenQ : (0 : ℚ) < den := by exact_mod_cast hden
        exact not_le_of_gt (div_neg_of_neg_of_pos hnum hdenQ)
      have hflag : ¬ binaryRatNonnegative
          ((⟨Int.negSucc n, den, hden⟩ : RawRat).value) = true :=
        fun h => hs ((binaryRatNonnegative_eq_true_iff _).1 h)
      rw [binaryRationalExpLower, if_neg hflag,
        binaryRationalNegativeExpLower]
      simp [RawRat.expApproxSteps, RawRat.expMagnitude,
        binaryRatNeg_eq_neg, binaryRatSub_eq_sub,
        binaryRatDiv_eq_div, binaryRatPow_eq_pow,
        RawRat.value_neg]
      ring

theorem machineBoundedRationalExpLowerCode_encode
    (guard : List Bool) (s loss : RawRat)
    (hsteps : RawRat.expApproxSteps s loss ≤ guard.length) :
    machineBoundedRationalExpLowerCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rationalBinaryCode (binaryRationalExpLower s.value loss.value) := by
  rw [machineBoundedRationalExpLowerCode,
    machineExpStepsRuler_encode guard s loss hsteps,
    machineExpBaseCode_encode,
    machineRationalPowerCode_encode]
  exact congrArg rationalBinaryCode
    (binaryNormalizeRawRat_expBasePow_eq s loss)

theorem machineBoundedRationalExpLowerRawEntryCode_encode
    (guard : List Bool) (s loss : RawRat)
    (hsteps : RawRat.expApproxSteps s loss ≤ guard.length) :
    machineBoundedRationalExpLowerRawEntryCode
        (pair guard (pair (rawRatBinaryCode s) (rawRatBinaryCode loss))) =
      rawRatBinaryCode
        (rawRatOfRat (binaryRationalExpLower s.value loss.value)) := by
  rw [machineBoundedRationalExpLowerRawEntryCode,
    machineBoundedRationalExpLowerRawPowerCode,
    machineExpStepsRuler_encode guard s loss hsteps,
    machineExpBaseCode_encode,
    machineRawRatPowerCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_expBasePow_eq]
  simp [rawRatBinaryCode, rawRatOfRat, rationalEntryBinaryCode]

end BeyondBethe
