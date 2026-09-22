/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineLengthBits
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalLogSeries
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare

/-!
# Polynomial-time directed rational logarithm

This file assembles the exact odd-series loop into the full dyadically
range-reduced lower and upper logarithms.  The precision is supplied as a
unary ruler.  Leading binary positions are read from word lengths, powers of
two are constructed directly as bitstrings, and all rational arithmetic is
performed by the verified unreduced-rational machines.
-/

namespace BeyondBethe

open Complexity

def rawRatTwoCode : List Bool := rawRatBinaryCode (RawRat.ofNat 2)

def machineDirectedLogRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDirectedLogArgumentCode (word : List Bool) : List Bool :=
  machinePairSecond word

def machineDirectedLogParameterNumeratorCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedLogArgumentCode word)
      (machineRawRatNegCode rawRatOneCode))

def machineDirectedLogParameterDenominatorCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedLogArgumentCode word) rawRatOneCode)

def machineDirectedLogParameterCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineDirectedLogParameterNumeratorCode word)
      (machineDirectedLogParameterDenominatorCode word))

def machineDirectedLogSeriesSumCode (word : List Bool) : List Bool :=
  machineRawRationalLogSeriesSumCode
    (pair (machineDirectedLogRuler word)
      (machineDirectedLogParameterCode word))

def machineDirectedLogUnitLowerRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode (pair rawRatTwoCode
    (machineDirectedLogSeriesSumCode word))

def machineDirectedLogOddPowerRuler (word : List Bool) : List Bool :=
  true :: (machineDirectedLogRuler word ++ machineDirectedLogRuler word)

def machineDirectedLogOddPowerCode (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineDirectedLogOddPowerRuler word)
      (machineDirectedLogParameterCode word))

def machineDirectedLogParameterSquareCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedLogParameterCode word)
      (machineDirectedLogParameterCode word))

def machineDirectedLogErrorDenominatorCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair rawRatOneCode
      (machineRawRatNegCode (machineDirectedLogParameterSquareCode word)))

def machineDirectedLogSeriesErrorCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair rawRatTwoCode
      (machineRawRatDivCode
        (pair (machineDirectedLogOddPowerCode word)
          (machineDirectedLogErrorDenominatorCode word))))

def machineDirectedLogUnitUpperRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedLogUnitLowerRawCode word)
      (machineDirectedLogSeriesErrorCode word))

theorem machineDirectedLogRuler_mem_FP :
    machineDirectedLogRuler ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineDirectedLogArgumentCode_mem_FP :
    machineDirectedLogArgumentCode ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineDirectedLogParameterNumeratorCode_mem_FP :
    machineDirectedLogParameterNumeratorCode ∈ Complexity.FP := by
  have hnegOne : (fun _ : List Bool => machineRawRatNegCode rawRatOneCode) ∈
      Complexity.FP := machineConst_mem_FP _
  have hpair := machinePair_mem_FP machineDirectedLogArgumentCode_mem_FP hnegOne
  simpa only [machineDirectedLogParameterNumeratorCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineDirectedLogParameterDenominatorCode_mem_FP :
    machineDirectedLogParameterDenominatorCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogArgumentCode_mem_FP
    (machineConst_mem_FP rawRatOneCode)
  simpa only [machineDirectedLogParameterDenominatorCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineDirectedLogParameterCode_mem_FP :
    machineDirectedLogParameterCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineDirectedLogParameterNumeratorCode_mem_FP
    machineDirectedLogParameterDenominatorCode_mem_FP
  simpa only [machineDirectedLogParameterCode] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineDirectedLogSeriesSumCode_mem_FP :
    machineDirectedLogSeriesSumCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogRuler_mem_FP
    machineDirectedLogParameterCode_mem_FP
  simpa only [machineDirectedLogSeriesSumCode] using!
    machineCompose_mem_FP hpair machineRawRationalLogSeriesSumCode_mem_FP

theorem machineDirectedLogUnitLowerRawCode_mem_FP :
    machineDirectedLogUnitLowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatTwoCode)
    machineDirectedLogSeriesSumCode_mem_FP
  simpa only [machineDirectedLogUnitLowerRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineDirectedLogOddPowerRuler_mem_FP :
    machineDirectedLogOddPowerRuler ∈ Complexity.FP := by
  have hdouble := machineAppend_mem_FP machineDirectedLogRuler_mem_FP
    machineDirectedLogRuler_mem_FP
  simpa only [machineDirectedLogOddPowerRuler] using!
    machineCompose_mem_FP hdouble (machinePrepend_mem_FP true)

theorem machineDirectedLogOddPowerCode_mem_FP :
    machineDirectedLogOddPowerCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogOddPowerRuler_mem_FP
    machineDirectedLogParameterCode_mem_FP
  simpa only [machineDirectedLogOddPowerCode] using!
    machineCompose_mem_FP hpair machineRawRatPowerCode_mem_FP

theorem machineDirectedLogParameterSquareCode_mem_FP :
    machineDirectedLogParameterSquareCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogParameterCode_mem_FP
    machineDirectedLogParameterCode_mem_FP
  simpa only [machineDirectedLogParameterSquareCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineDirectedLogErrorDenominatorCode_mem_FP :
    machineDirectedLogErrorDenominatorCode ∈ Complexity.FP := by
  have hneg := machineCompose_mem_FP
    machineDirectedLogParameterSquareCode_mem_FP machineRawRatNegCode_mem_FP
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatOneCode) hneg
  simpa only [machineDirectedLogErrorDenominatorCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineDirectedLogSeriesErrorCode_mem_FP :
    machineDirectedLogSeriesErrorCode ∈ Complexity.FP := by
  have hratioPair := machinePair_mem_FP machineDirectedLogOddPowerCode_mem_FP
    machineDirectedLogErrorDenominatorCode_mem_FP
  have hratio := machineCompose_mem_FP hratioPair machineRawRatDivCode_mem_FP
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatTwoCode) hratio
  simpa only [machineDirectedLogSeriesErrorCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineDirectedLogUnitUpperRawCode_mem_FP :
    machineDirectedLogUnitUpperRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogUnitLowerRawCode_mem_FP
    machineDirectedLogSeriesErrorCode_mem_FP
  simpa only [machineDirectedLogUnitUpperRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

/-! ## Dyadic range reduction -/

def machineDirectedLogNumeratorAbsBits (word : List Bool) : List Bool :=
  machineIntegerNatAbsBits (machinePairFirst (machineDirectedLogArgumentCode word))

def machineDirectedLogDenominatorBits (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedLogArgumentCode word)

def machineDirectedLogNumeratorLogRuler (word : List Bool) : List Bool :=
  (machineDirectedLogNumeratorAbsBits word).tail

def machineDirectedLogDenominatorLogRuler (word : List Bool) : List Bool :=
  (machineDirectedLogDenominatorBits word).tail

def machineDirectedLogNumeratorLogBits (word : List Bool) : List Bool :=
  machineLengthBits (machineDirectedLogNumeratorLogRuler word)

def machineDirectedLogDenominatorLogBits (word : List Bool) : List Bool :=
  machineLengthBits (machineDirectedLogDenominatorLogRuler word)

def machineDirectedLogExponentIntegerCode (word : List Bool) : List Bool :=
  machineIntegerAddCode
    (pair (machineNaturalIntegerCode (machineDirectedLogNumeratorLogBits word))
      (machineIntegerNegCode
        (machineNaturalIntegerCode (machineDirectedLogDenominatorLogBits word))))

def machineDirectedLogPowerTwoBits (ruler : List Bool) : List Bool :=
  List.replicate ruler.length false ++ [true]

def machineDirectedLogScaleCode (word : List Bool) : List Bool :=
  pair
    (machineNaturalIntegerCode
      (machineDirectedLogPowerTwoBits
        (machineDirectedLogNumeratorLogRuler word)))
    (machineDirectedLogPowerTwoBits
      (machineDirectedLogDenominatorLogRuler word))

def machineDirectedLogResidualCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineDirectedLogArgumentCode word)
      (machineDirectedLogScaleCode word))

def machineDirectedLogResidualAtLeastOne (word : List Bool) : List Bool :=
  machineRawRatLeBit (pair rawRatOneCode (machineDirectedLogResidualCode word))

def machineDirectedLogUnitCode (word : List Bool) : List Bool :=
  machineIfHead (machineDirectedLogResidualAtLeastOne word)
    (machineDirectedLogResidualCode word)
    (machineRawRatInvCode (machineDirectedLogResidualCode word))

def machineDirectedLogTwoInput (word : List Bool) : List Bool :=
  pair (machineDirectedLogRuler word) rawRatTwoCode

def machineDirectedLogUnitInput (word : List Bool) : List Bool :=
  pair (machineDirectedLogRuler word) (machineDirectedLogUnitCode word)

def machineDirectedLogExponentRawRatCode (word : List Bool) : List Bool :=
  pair (machineDirectedLogExponentIntegerCode word) [true]

def machineDirectedLogIntegerLowerCode (word : List Bool) : List Bool :=
  let lo := machineDirectedLogUnitLowerRawCode (machineDirectedLogTwoInput word)
  let hi := machineDirectedLogUnitUpperRawCode (machineDirectedLogTwoInput word)
  let factor := machineIfHead (machineHeadBit
    (machineDirectedLogExponentIntegerCode word)) hi lo
  machineRawRatMulCode
    (pair (machineDirectedLogExponentRawRatCode word) factor)

def machineDirectedLogIntegerUpperCode (word : List Bool) : List Bool :=
  let lo := machineDirectedLogUnitLowerRawCode (machineDirectedLogTwoInput word)
  let hi := machineDirectedLogUnitUpperRawCode (machineDirectedLogTwoInput word)
  let factor := machineIfHead (machineHeadBit
    (machineDirectedLogExponentIntegerCode word)) lo hi
  machineRawRatMulCode
    (pair (machineDirectedLogExponentRawRatCode word) factor)

def machineDirectedLogResidualLowerCode (word : List Bool) : List Bool :=
  let lo := machineDirectedLogUnitLowerRawCode (machineDirectedLogUnitInput word)
  let hi := machineDirectedLogUnitUpperRawCode (machineDirectedLogUnitInput word)
  machineIfHead (machineDirectedLogResidualAtLeastOne word) lo
    (machineRawRatNegCode hi)

def machineDirectedLogResidualUpperCode (word : List Bool) : List Bool :=
  let lo := machineDirectedLogUnitLowerRawCode (machineDirectedLogUnitInput word)
  let hi := machineDirectedLogUnitUpperRawCode (machineDirectedLogUnitInput word)
  machineIfHead (machineDirectedLogResidualAtLeastOne word) hi
    (machineRawRatNegCode lo)

def machineDirectedLogLowerRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedLogIntegerLowerCode word)
      (machineDirectedLogResidualLowerCode word))

def machineDirectedLogUpperRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedLogIntegerUpperCode word)
      (machineDirectedLogResidualUpperCode word))

def machineDirectedLogLowerCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineDirectedLogLowerRawCode word)

def machineDirectedLogUpperCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineDirectedLogUpperRawCode word)

theorem machineDirectedLogNumeratorAbsBits_mem_FP :
    machineDirectedLogNumeratorAbsBits ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineDirectedLogArgumentCode_mem_FP
    machinePairFirst_mem_FP
  simpa only [machineDirectedLogNumeratorAbsBits] using!
    machineCompose_mem_FP hnum machineIntegerNatAbsBits_mem_FP

theorem machineDirectedLogDenominatorBits_mem_FP :
    machineDirectedLogDenominatorBits ∈ Complexity.FP := by
  simpa only [machineDirectedLogDenominatorBits] using!
    machineCompose_mem_FP machineDirectedLogArgumentCode_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedLogNumeratorLogRuler_mem_FP :
    machineDirectedLogNumeratorLogRuler ∈ Complexity.FP := by
  simpa only [machineDirectedLogNumeratorLogRuler] using!
    machineCompose_mem_FP machineDirectedLogNumeratorAbsBits_mem_FP
      machineTail_mem_FP

theorem machineDirectedLogDenominatorLogRuler_mem_FP :
    machineDirectedLogDenominatorLogRuler ∈ Complexity.FP := by
  simpa only [machineDirectedLogDenominatorLogRuler] using!
    machineCompose_mem_FP machineDirectedLogDenominatorBits_mem_FP
      machineTail_mem_FP

theorem machineDirectedLogNumeratorLogBits_mem_FP :
    machineDirectedLogNumeratorLogBits ∈ Complexity.FP := by
  simpa only [machineDirectedLogNumeratorLogBits] using!
    machineCompose_mem_FP machineDirectedLogNumeratorLogRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineDirectedLogDenominatorLogBits_mem_FP :
    machineDirectedLogDenominatorLogBits ∈ Complexity.FP := by
  simpa only [machineDirectedLogDenominatorLogBits] using!
    machineCompose_mem_FP machineDirectedLogDenominatorLogRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineDirectedLogExponentIntegerCode_mem_FP :
    machineDirectedLogExponentIntegerCode ∈ Complexity.FP := by
  have hnum := machineCompose_mem_FP machineDirectedLogNumeratorLogBits_mem_FP
    (machinePrepend_mem_FP false)
  have hdenNat := machineCompose_mem_FP
    machineDirectedLogDenominatorLogBits_mem_FP (machinePrepend_mem_FP false)
  have hden := machineCompose_mem_FP hdenNat machineIntegerNegCode_mem_FP
  have hpair := machinePair_mem_FP hnum hden
  simpa only [machineDirectedLogExponentIntegerCode] using!
    machineCompose_mem_FP hpair machineIntegerAddCode_mem_FP

theorem machineDirectedLogPowerTwoBits_mem_FP :
    machineDirectedLogPowerTwoBits ∈ Complexity.FP := by
  have hzero := machineZeroBlock_mem_FP
  have hone : (fun _ : List Bool => [true]) ∈ Complexity.FP :=
    machineConst_mem_FP [true]
  simpa only [machineDirectedLogPowerTwoBits] using!
    machineAppend_mem_FP hzero hone

theorem machineDirectedLogScaleCode_mem_FP :
    machineDirectedLogScaleCode ∈ Complexity.FP := by
  have hnumBits := machineCompose_mem_FP
    machineDirectedLogNumeratorLogRuler_mem_FP
    machineDirectedLogPowerTwoBits_mem_FP
  have hnum := machineCompose_mem_FP hnumBits (machinePrepend_mem_FP false)
  have hden := machineCompose_mem_FP
    machineDirectedLogDenominatorLogRuler_mem_FP
    machineDirectedLogPowerTwoBits_mem_FP
  exact machinePair_mem_FP hnum hden

theorem machineDirectedLogResidualCode_mem_FP :
    machineDirectedLogResidualCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogArgumentCode_mem_FP
    machineDirectedLogScaleCode_mem_FP
  simpa only [machineDirectedLogResidualCode] using!
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineDirectedLogResidualAtLeastOne_mem_FP :
    machineDirectedLogResidualAtLeastOne ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatOneCode)
    machineDirectedLogResidualCode_mem_FP
  simpa only [machineDirectedLogResidualAtLeastOne] using!
    machineCompose_mem_FP hpair machineRawRatLeBit_mem_FP

theorem machineDirectedLogUnitCode_mem_FP :
    machineDirectedLogUnitCode ∈ Complexity.FP := by
  have hinv := machineCompose_mem_FP machineDirectedLogResidualCode_mem_FP
    machineRawRatInvCode_mem_FP
  simpa only [machineDirectedLogUnitCode] using!
    machineIfHead_mem_FP machineDirectedLogResidualAtLeastOne_mem_FP
      machineDirectedLogResidualCode_mem_FP hinv

theorem machineDirectedLogTwoInput_mem_FP :
    machineDirectedLogTwoInput ∈ Complexity.FP :=
  machinePair_mem_FP machineDirectedLogRuler_mem_FP
    (machineConst_mem_FP rawRatTwoCode)

theorem machineDirectedLogUnitInput_mem_FP :
    machineDirectedLogUnitInput ∈ Complexity.FP :=
  machinePair_mem_FP machineDirectedLogRuler_mem_FP
    machineDirectedLogUnitCode_mem_FP

theorem machineDirectedLogExponentRawRatCode_mem_FP :
    machineDirectedLogExponentRawRatCode ∈ Complexity.FP :=
  machinePair_mem_FP machineDirectedLogExponentIntegerCode_mem_FP
    (machineConst_mem_FP [true])

theorem machineDirectedLogIntegerLowerCode_mem_FP :
    machineDirectedLogIntegerLowerCode ∈ Complexity.FP := by
  have hlo := machineCompose_mem_FP machineDirectedLogTwoInput_mem_FP
    machineDirectedLogUnitLowerRawCode_mem_FP
  have hhi := machineCompose_mem_FP machineDirectedLogTwoInput_mem_FP
    machineDirectedLogUnitUpperRawCode_mem_FP
  have hsign := machineCompose_mem_FP
    machineDirectedLogExponentIntegerCode_mem_FP machineHeadBit_mem_FP
  have hfactor := machineIfHead_mem_FP hsign hhi hlo
  have hpair := machinePair_mem_FP
    machineDirectedLogExponentRawRatCode_mem_FP hfactor
  simpa only [machineDirectedLogIntegerLowerCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineDirectedLogIntegerUpperCode_mem_FP :
    machineDirectedLogIntegerUpperCode ∈ Complexity.FP := by
  have hlo := machineCompose_mem_FP machineDirectedLogTwoInput_mem_FP
    machineDirectedLogUnitLowerRawCode_mem_FP
  have hhi := machineCompose_mem_FP machineDirectedLogTwoInput_mem_FP
    machineDirectedLogUnitUpperRawCode_mem_FP
  have hsign := machineCompose_mem_FP
    machineDirectedLogExponentIntegerCode_mem_FP machineHeadBit_mem_FP
  have hfactor := machineIfHead_mem_FP hsign hlo hhi
  have hpair := machinePair_mem_FP
    machineDirectedLogExponentRawRatCode_mem_FP hfactor
  simpa only [machineDirectedLogIntegerUpperCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineDirectedLogResidualLowerCode_mem_FP :
    machineDirectedLogResidualLowerCode ∈ Complexity.FP := by
  have hlo := machineCompose_mem_FP machineDirectedLogUnitInput_mem_FP
    machineDirectedLogUnitLowerRawCode_mem_FP
  have hhi := machineCompose_mem_FP machineDirectedLogUnitInput_mem_FP
    machineDirectedLogUnitUpperRawCode_mem_FP
  have hnegHi := machineCompose_mem_FP hhi machineRawRatNegCode_mem_FP
  simpa only [machineDirectedLogResidualLowerCode] using!
    machineIfHead_mem_FP machineDirectedLogResidualAtLeastOne_mem_FP
      hlo hnegHi

theorem machineDirectedLogResidualUpperCode_mem_FP :
    machineDirectedLogResidualUpperCode ∈ Complexity.FP := by
  have hlo := machineCompose_mem_FP machineDirectedLogUnitInput_mem_FP
    machineDirectedLogUnitLowerRawCode_mem_FP
  have hhi := machineCompose_mem_FP machineDirectedLogUnitInput_mem_FP
    machineDirectedLogUnitUpperRawCode_mem_FP
  have hnegLo := machineCompose_mem_FP hlo machineRawRatNegCode_mem_FP
  simpa only [machineDirectedLogResidualUpperCode] using!
    machineIfHead_mem_FP machineDirectedLogResidualAtLeastOne_mem_FP
      hhi hnegLo

theorem machineDirectedLogLowerRawCode_mem_FP :
    machineDirectedLogLowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogIntegerLowerCode_mem_FP
    machineDirectedLogResidualLowerCode_mem_FP
  simpa only [machineDirectedLogLowerRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineDirectedLogUpperRawCode_mem_FP :
    machineDirectedLogUpperRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogIntegerUpperCode_mem_FP
    machineDirectedLogResidualUpperCode_mem_FP
  simpa only [machineDirectedLogUpperRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineDirectedLogLowerCode_mem_FP :
    machineDirectedLogLowerCode ∈ Complexity.FP := by
  simpa only [machineDirectedLogLowerCode] using!
    machineCompose_mem_FP machineDirectedLogLowerRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineDirectedLogUpperCode_mem_FP :
    machineDirectedLogUpperCode ∈ Complexity.FP := by
  simpa only [machineDirectedLogUpperCode] using!
    machineCompose_mem_FP machineDirectedLogUpperRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

/-! ## Exact unit-interval semantics -/

namespace RawRat

def logUnitParameter (y : RawRat) : RawRat :=
  (y.add one.neg).div (y.add one)

def logUnitLower (y : RawRat) (N : ℕ) : RawRat :=
  (ofNat 2).mul (logSeriesSum (logUnitParameter y) N)

def logSeriesError (y : RawRat) (N : ℕ) : RawRat :=
  let x := logUnitParameter y
  (ofNat 2).mul ((x.pow (2 * N + 1)).div (one.add (x.mul x).neg))

def logUnitUpper (y : RawRat) (N : ℕ) : RawRat :=
  (logUnitLower y N).add (logSeriesError y N)

@[simp] theorem value_logUnitParameter (y : RawRat) :
    (logUnitParameter y).value = binaryRationalLogUnitParameter y.value := by
  simp [logUnitParameter, binaryRationalLogUnitParameter,
    binaryRatDiv_eq_div, binaryRatSub_eq_sub, binaryRatAdd_eq_add,
    sub_eq_add_neg]

@[simp] theorem value_logUnitLower (y : RawRat) (N : ℕ) :
    (logUnitLower y N).value = binaryDirectedLogUnitLower y.value N := by
  simp [logUnitLower, binaryDirectedLogUnitLower,
    binaryRationalLogSeries, binaryRatMul_eq_mul,
    RawRat.value_logSeriesSum]

@[simp] theorem value_logSeriesError (y : RawRat) (N : ℕ) :
    (logSeriesError y N).value =
      binaryRationalLogSeriesError (binaryRationalLogUnitParameter y.value) N := by
  simp [logSeriesError, binaryRationalLogSeriesError,
    binaryRatMul_eq_mul, binaryRatDiv_eq_div, binaryRatSub_eq_sub,
    binaryRatPow_eq_pow]
  ring

@[simp] theorem value_logUnitUpper (y : RawRat) (N : ℕ) :
    (logUnitUpper y N).value = binaryDirectedLogUnitUpper y.value N := by
  simp [logUnitUpper, binaryDirectedLogUnitUpper,
    binaryDirectedLogUnitLower, binaryRatAdd_eq_add]

end RawRat

@[simp] theorem machineDirectedLogParameterCode_encode
    (ruler : List Bool) (y : RawRat) :
    machineDirectedLogParameterCode (pair ruler (rawRatBinaryCode y)) =
      rawRatBinaryCode (RawRat.logUnitParameter y) := by
  rw [machineDirectedLogParameterCode,
    machineDirectedLogParameterNumeratorCode,
    machineDirectedLogParameterDenominatorCode]
  simp only [machineDirectedLogArgumentCode, machinePairSecond_pair,
    rawRatOneCode, machineRawRatNegCode_encode,
    machineRawRatAddCode_encode, machineRawRatDivCode_encode,
    RawRat.logUnitParameter]

@[simp] theorem machineDirectedLogSeriesSumCode_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogSeriesSumCode
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      rawRatBinaryCode
        (RawRat.logSeriesSum (RawRat.logUnitParameter y) N) := by
  rw [machineDirectedLogSeriesSumCode]
  simp only [machineDirectedLogRuler, machinePairFirst_pair,
    machineDirectedLogParameterCode_encode,
    machineRawRationalLogSeriesSumCode_encode]

@[simp] theorem machineDirectedLogUnitLowerRawCode_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogUnitLowerRawCode
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      rawRatBinaryCode (RawRat.logUnitLower y N) := by
  rw [machineDirectedLogUnitLowerRawCode]
  simp only [rawRatTwoCode, machineDirectedLogSeriesSumCode_encode,
    machineRawRatMulCode_encode, RawRat.logUnitLower]

theorem machineDirectedLogOddPowerRuler_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogOddPowerRuler
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      List.replicate (2 * N + 1) true := by
  rw [machineDirectedLogOddPowerRuler]
  simp only [machineDirectedLogRuler, machinePairFirst_pair]
  rw [← List.replicate_add]
  rw [show 2 * N + 1 = (N + N) + 1 by omega, List.replicate_succ]

@[simp] theorem machineDirectedLogOddPowerCode_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogOddPowerCode
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      rawRatBinaryCode
        ((RawRat.logUnitParameter y).pow (2 * N + 1)) := by
  rw [machineDirectedLogOddPowerCode,
    machineDirectedLogOddPowerRuler_encode,
    machineDirectedLogParameterCode_encode,
    machineRawRatPowerCode_encode]

@[simp] theorem machineDirectedLogParameterSquareCode_encode
    (ruler : List Bool) (y : RawRat) :
    machineDirectedLogParameterSquareCode
        (pair ruler (rawRatBinaryCode y)) =
      rawRatBinaryCode
        ((RawRat.logUnitParameter y).mul (RawRat.logUnitParameter y)) := by
  rw [machineDirectedLogParameterSquareCode]
  simp only [machineDirectedLogParameterCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedLogErrorDenominatorCode_encode
    (ruler : List Bool) (y : RawRat) :
    machineDirectedLogErrorDenominatorCode
        (pair ruler (rawRatBinaryCode y)) =
      rawRatBinaryCode
        (RawRat.one.add
          ((RawRat.logUnitParameter y).mul
            (RawRat.logUnitParameter y)).neg) := by
  rw [machineDirectedLogErrorDenominatorCode]
  simp only [rawRatOneCode, machineDirectedLogParameterSquareCode_encode,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode]

@[simp] theorem machineDirectedLogSeriesErrorCode_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogSeriesErrorCode
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      rawRatBinaryCode (RawRat.logSeriesError y N) := by
  rw [machineDirectedLogSeriesErrorCode]
  simp only [rawRatTwoCode, machineDirectedLogOddPowerCode_encode,
    machineDirectedLogErrorDenominatorCode_encode,
    machineRawRatDivCode_encode, machineRawRatMulCode_encode,
    RawRat.logSeriesError]

@[simp] theorem machineDirectedLogUnitUpperRawCode_encode
    (y : RawRat) (N : ℕ) :
    machineDirectedLogUnitUpperRawCode
        (pair (List.replicate N true) (rawRatBinaryCode y)) =
      rawRatBinaryCode (RawRat.logUnitUpper y N) := by
  rw [machineDirectedLogUnitUpperRawCode]
  simp only [machineDirectedLogUnitLowerRawCode_encode,
    machineDirectedLogSeriesErrorCode_encode,
    machineRawRatAddCode_encode, RawRat.logUnitUpper]

@[simp] theorem machineDirectedLogTwoLowerRawCode_encode (N : ℕ) :
    machineDirectedLogUnitLowerRawCode
        (pair (List.replicate N true) rawRatTwoCode) =
      rawRatBinaryCode (RawRat.logUnitLower (RawRat.ofNat 2) N) := by
  simpa only [rawRatTwoCode] using!
    machineDirectedLogUnitLowerRawCode_encode (RawRat.ofNat 2) N

@[simp] theorem machineDirectedLogTwoUpperRawCode_encode (N : ℕ) :
    machineDirectedLogUnitUpperRawCode
        (pair (List.replicate N true) rawRatTwoCode) =
      rawRatBinaryCode (RawRat.logUnitUpper (RawRat.ofNat 2) N) := by
  simpa only [rawRatTwoCode] using!
    machineDirectedLogUnitUpperRawCode_encode (RawRat.ofNat 2) N

private theorem directedLogPowerTwoBits_value : ∀ k : ℕ,
    Nat.fromBitsLE (List.replicate k false ++ [true]) = 2 ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append,
        Nat.fromBitsLE_cons, Bool.false_eq, ih,
        pow_succ]
      norm_num
      ring

@[simp] theorem machineDirectedLogPowerTwoBits_encode (ruler : List Bool) :
    machineDirectedLogPowerTwoBits ruler = (2 ^ ruler.length).bits := by
  apply Nat.fromBitsLE_inj_of_length_eq
  · simp [machineDirectedLogPowerTwoBits, Nat.size_eq_bits_len,
      Nat.size_pow]
  · rw [machineDirectedLogPowerTwoBits, directedLogPowerTwoBits_value,
      Nat.fromBitsLE_bits]

@[simp] theorem machineDirectedLogNumeratorAbsBits_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogNumeratorAbsBits
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) = q.num.natAbs.bits := by
  rw [machineDirectedLogNumeratorAbsBits]
  simp only [machineDirectedLogArgumentCode, machinePairSecond_pair,
    rawRatBinaryCode, machinePairFirst_pair,
    machineIntegerNatAbsBits_encode, rawRatOfRat]

@[simp] theorem machineDirectedLogDenominatorBits_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogDenominatorBits
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) = q.den.bits := by
  simp [machineDirectedLogDenominatorBits, machineDirectedLogArgumentCode,
    rawRatBinaryCode, rawRatOfRat]

theorem machineDirectedLogNumeratorLogRuler_length
    (ruler : List Bool) (q : ℚ) :
    (machineDirectedLogNumeratorLogRuler
      (pair ruler (rawRatBinaryCode (rawRatOfRat q)))).length =
        binaryNatLog2 q.num.natAbs := by
  rw [machineDirectedLogNumeratorLogRuler,
    machineDirectedLogNumeratorAbsBits_encode]
  simp [binaryNatLog2, Nat.size_eq_bits_len]

theorem machineDirectedLogDenominatorLogRuler_length
    (ruler : List Bool) (q : ℚ) :
    (machineDirectedLogDenominatorLogRuler
      (pair ruler (rawRatBinaryCode (rawRatOfRat q)))).length =
        binaryNatLog2 q.den := by
  rw [machineDirectedLogDenominatorLogRuler,
    machineDirectedLogDenominatorBits_encode]
  simp [binaryNatLog2, Nat.size_eq_bits_len]

@[simp] theorem machineDirectedLogNumeratorLogBits_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogNumeratorLogBits
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      (binaryNatLog2 q.num.natAbs).bits := by
  rw [machineDirectedLogNumeratorLogBits, machineLengthBits_encode,
    machineDirectedLogNumeratorLogRuler_length]

@[simp] theorem machineDirectedLogDenominatorLogBits_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogDenominatorLogBits
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      (binaryNatLog2 q.den).bits := by
  rw [machineDirectedLogDenominatorLogBits, machineLengthBits_encode,
    machineDirectedLogDenominatorLogRuler_length]

@[simp] theorem machineDirectedLogExponentIntegerCode_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogExponentIntegerCode
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      integerBinaryCode (binaryRationalBinaryExponent q) := by
  rw [machineDirectedLogExponentIntegerCode]
  simp only [machineDirectedLogNumeratorLogBits_encode,
    machineDirectedLogDenominatorLogBits_encode,
    machineNaturalIntegerCode_natBits, machineIntegerNegCode_encode,
    machineIntegerAddCode_encode, binaryRationalBinaryExponent]
  congr 1

namespace RawRat

def logScale (q : ℚ) : RawRat :=
  ⟨(2 ^ binaryNatLog2 q.num.natAbs : ℕ),
    2 ^ binaryNatLog2 q.den, by positivity⟩

def logResidual (q : ℚ) : RawRat :=
  (rawRatOfRat q).div (logScale q)

def logUnit (q : ℚ) : RawRat :=
  if 1 ≤ (logResidual q).value then logResidual q else (logResidual q).inv

@[simp] theorem value_logScale (q : ℚ) :
    (logScale q).value = binaryRationalBinaryScale q := by
  simp [logScale, binaryRationalBinaryScale, binaryRatDiv_eq_div,
    binaryRatPow_eq_pow, value]

@[simp] theorem value_logResidual (q : ℚ) :
    (logResidual q).value = binaryRationalBinaryResidual q := by
  simp [logResidual, binaryRationalBinaryResidual,
    binaryRatDiv_eq_div]

@[simp] theorem value_logUnit (q : ℚ) :
    (logUnit q).value = binaryRationalLogUnit q := by
  rw [logUnit, binaryRationalLogUnit]
  by_cases h : binaryRationalBinaryResidual q < 1
  · have hnot : ¬ 1 ≤ (logResidual q).value := by simpa using! h
    rw [ite_eq_left ((binaryRatLt_eq_true_iff _ _).2 h), ite_eq_right hnot]
    simp [binaryRatInv_eq_inv]
  · have hle : 1 ≤ (logResidual q).value := by
      simpa using! (le_of_not_gt h)
    have hflag : ¬ binaryRatLt (binaryRationalBinaryResidual q) 1 = true :=
      fun htrue => h ((binaryRatLt_eq_true_iff _ _).1 htrue)
    rw [ite_eq_right hflag, ite_eq_left hle]
    exact RawRat.value_logResidual q

end RawRat

@[simp] theorem machineDirectedLogScaleCode_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogScaleCode
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logScale q) := by
  rw [machineDirectedLogScaleCode]
  rw [machineDirectedLogPowerTwoBits_encode,
    machineDirectedLogPowerTwoBits_encode,
    machineDirectedLogNumeratorLogRuler_length,
    machineDirectedLogDenominatorLogRuler_length,
    machineNaturalIntegerCode_natBits]
  rfl

@[simp] theorem machineDirectedLogResidualCode_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogResidualCode
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logResidual q) := by
  rw [machineDirectedLogResidualCode]
  simp only [machineDirectedLogArgumentCode, machinePairSecond_pair,
    machineDirectedLogScaleCode_encode,
    machineRawRatDivCode_encode, RawRat.logResidual]

@[simp] theorem machineDirectedLogResidualAtLeastOne_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogResidualAtLeastOne
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      [decide (1 ≤ binaryRationalBinaryResidual q)] := by
  rw [machineDirectedLogResidualAtLeastOne]
  simp only [rawRatOneCode, machineDirectedLogResidualCode_encode,
    machineRawRatLeBit_encode, RawRat.value_one,
    RawRat.value_logResidual]

@[simp] theorem machineDirectedLogUnitCode_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogUnitCode
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logUnit q) := by
  rw [machineDirectedLogUnitCode]
  simp only [machineDirectedLogResidualAtLeastOne_encode,
    machineDirectedLogResidualCode_encode]
  by_cases h : 1 ≤ binaryRationalBinaryResidual q
  · simp [h, RawRat.logUnit]
  · rw [show decide (1 ≤ binaryRationalBinaryResidual q) = false by simp [h]]
    simp only [machineIfHead_false, machineRawRatInvCode_encode]
    simp [RawRat.logUnit, h]

namespace RawRat

def ofInt (z : ℤ) : RawRat := ⟨z, 1, by omega⟩

@[simp] theorem value_ofInt (z : ℤ) : (ofInt z).value = z := by
  simp [ofInt, value]

def logIntegerLower (q : ℚ) (N : ℕ) : RawRat :=
  let k := binaryRationalBinaryExponent q
  (ofInt k).mul
    (if 0 ≤ k then logUnitLower (ofNat 2) N
      else logUnitUpper (ofNat 2) N)

def logIntegerUpper (q : ℚ) (N : ℕ) : RawRat :=
  let k := binaryRationalBinaryExponent q
  (ofInt k).mul
    (if 0 ≤ k then logUnitUpper (ofNat 2) N
      else logUnitLower (ofNat 2) N)

def logResidualLower (q : ℚ) (N : ℕ) : RawRat :=
  if 1 ≤ (logResidual q).value then logUnitLower (logUnit q) N
  else (logUnitUpper (logUnit q) N).neg

def logResidualUpper (q : ℚ) (N : ℕ) : RawRat :=
  if 1 ≤ (logResidual q).value then logUnitUpper (logUnit q) N
  else (logUnitLower (logUnit q) N).neg

def logLower (q : ℚ) (N : ℕ) : RawRat :=
  (logIntegerLower q N).add (logResidualLower q N)

def logUpper (q : ℚ) (N : ℕ) : RawRat :=
  (logIntegerUpper q N).add (logResidualUpper q N)

@[simp] theorem value_logIntegerLower (q : ℚ) (N : ℕ) :
    (logIntegerLower q N).value =
      binaryDirectedIntMulLower (binaryRationalBinaryExponent q)
        (binaryDirectedLogUnitLower 2 N)
        (binaryDirectedLogUnitUpper 2 N) := by
  rw [logIntegerLower, value_mul, value_ofInt,
    binaryDirectedIntMulLower]
  split_ifs <;> simp [binaryRatMul_eq_mul]

@[simp] theorem value_logIntegerUpper (q : ℚ) (N : ℕ) :
    (logIntegerUpper q N).value =
      binaryDirectedIntMulUpper (binaryRationalBinaryExponent q)
        (binaryDirectedLogUnitLower 2 N)
        (binaryDirectedLogUnitUpper 2 N) := by
  rw [logIntegerUpper, value_mul, value_ofInt,
    binaryDirectedIntMulUpper]
  split_ifs <;> simp [binaryRatMul_eq_mul]

@[simp] theorem value_logResidualLower (q : ℚ) (N : ℕ) :
    (logResidualLower q N).value =
      if binaryRatLt (binaryRationalBinaryResidual q) 1 then
        binaryRatNeg (binaryDirectedLogUnitUpper (binaryRationalLogUnit q) N)
      else binaryDirectedLogUnitLower (binaryRationalLogUnit q) N := by
  rw [logResidualLower]
  by_cases h : binaryRationalBinaryResidual q < 1
  · have hnot : ¬ 1 ≤ (logResidual q).value := by simpa using! h
    rw [ite_eq_right hnot,
      ite_eq_left ((binaryRatLt_eq_true_iff _ _).2 h)]
    simp [binaryRatNeg_eq_neg]
  · have hle : 1 ≤ (logResidual q).value := by
      simpa using! (le_of_not_gt h)
    have hflag : ¬ binaryRatLt (binaryRationalBinaryResidual q) 1 = true :=
      fun htrue => h ((binaryRatLt_eq_true_iff _ _).1 htrue)
    rw [ite_eq_left hle, ite_eq_right hflag]
    simpa only [value_logUnit] using! value_logUnitLower (logUnit q) N

@[simp] theorem value_logResidualUpper (q : ℚ) (N : ℕ) :
    (logResidualUpper q N).value =
      if binaryRatLt (binaryRationalBinaryResidual q) 1 then
        binaryRatNeg (binaryDirectedLogUnitLower (binaryRationalLogUnit q) N)
      else binaryDirectedLogUnitUpper (binaryRationalLogUnit q) N := by
  rw [logResidualUpper]
  by_cases h : binaryRationalBinaryResidual q < 1
  · have hnot : ¬ 1 ≤ (logResidual q).value := by simpa using! h
    rw [ite_eq_right hnot,
      ite_eq_left ((binaryRatLt_eq_true_iff _ _).2 h)]
    simp [binaryRatNeg_eq_neg]
  · have hle : 1 ≤ (logResidual q).value := by
      simpa using! (le_of_not_gt h)
    have hflag : ¬ binaryRatLt (binaryRationalBinaryResidual q) 1 = true :=
      fun htrue => h ((binaryRatLt_eq_true_iff _ _).1 htrue)
    rw [ite_eq_left hle, ite_eq_right hflag]
    simpa only [value_logUnit] using! value_logUnitUpper (logUnit q) N

@[simp] theorem value_logLower (q : ℚ) (N : ℕ) :
    (logLower q N).value = binaryDirectedLogLower q N := by
  simp [logLower, binaryDirectedLogLower, binaryRatAdd_eq_add]

@[simp] theorem value_logUpper (q : ℚ) (N : ℕ) :
    (logUpper q N).value = binaryDirectedLogUpper q N := by
  simp [logUpper, binaryDirectedLogUpper, binaryRatAdd_eq_add]

end RawRat

@[simp] theorem machineDirectedLogExponentRawRatCode_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogExponentRawRatCode
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode
        (RawRat.ofInt (binaryRationalBinaryExponent q)) := by
  rw [machineDirectedLogExponentRawRatCode,
    machineDirectedLogExponentIntegerCode_encode]
  simp [rawRatBinaryCode, RawRat.ofInt]

@[simp] theorem machineDirectedLogTwoInput_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogTwoInput
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      pair (List.replicate N true) rawRatTwoCode := by
  simp [machineDirectedLogTwoInput, machineDirectedLogRuler]

@[simp] theorem machineDirectedLogUnitInput_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogUnitInput
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      pair (List.replicate N true) (rawRatBinaryCode (RawRat.logUnit q)) := by
  simp [machineDirectedLogUnitInput, machineDirectedLogRuler]

@[simp] theorem machineDirectedLogIntegerLowerCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogIntegerLowerCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logIntegerLower q N) := by
  cases hk : binaryRationalBinaryExponent q with
  | ofNat k =>
      simp [machineDirectedLogIntegerLowerCode,
        machineDirectedLogTwoInput_encode,
        machineDirectedLogExponentIntegerCode_encode,
        machineDirectedLogExponentRawRatCode_encode,
        machineDirectedLogTwoLowerRawCode_encode,
        machineDirectedLogTwoUpperRawCode_encode,
        machineRawRatMulCode_encode, RawRat.logIntegerLower, hk,
        integerBinaryCode]
  | negSucc k =>
      simp [machineDirectedLogIntegerLowerCode,
        machineDirectedLogTwoInput_encode,
        machineDirectedLogExponentIntegerCode_encode,
        machineDirectedLogExponentRawRatCode_encode,
        machineDirectedLogTwoLowerRawCode_encode,
        machineDirectedLogTwoUpperRawCode_encode,
        machineRawRatMulCode_encode, RawRat.logIntegerLower, hk,
        integerBinaryCode]

@[simp] theorem machineDirectedLogIntegerUpperCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogIntegerUpperCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logIntegerUpper q N) := by
  cases hk : binaryRationalBinaryExponent q with
  | ofNat k =>
      simp [machineDirectedLogIntegerUpperCode,
        machineDirectedLogTwoInput_encode,
        machineDirectedLogExponentIntegerCode_encode,
        machineDirectedLogExponentRawRatCode_encode,
        machineDirectedLogTwoLowerRawCode_encode,
        machineDirectedLogTwoUpperRawCode_encode,
        machineRawRatMulCode_encode, RawRat.logIntegerUpper, hk,
        integerBinaryCode]
  | negSucc k =>
      simp [machineDirectedLogIntegerUpperCode,
        machineDirectedLogTwoInput_encode,
        machineDirectedLogExponentIntegerCode_encode,
        machineDirectedLogExponentRawRatCode_encode,
        machineDirectedLogTwoLowerRawCode_encode,
        machineDirectedLogTwoUpperRawCode_encode,
        machineRawRatMulCode_encode, RawRat.logIntegerUpper, hk,
        integerBinaryCode]

@[simp] theorem machineDirectedLogResidualLowerCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogResidualLowerCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logResidualLower q N) := by
  rw [machineDirectedLogResidualLowerCode]
  simp only [machineDirectedLogUnitInput_encode,
    machineDirectedLogUnitLowerRawCode_encode,
    machineDirectedLogUnitUpperRawCode_encode,
    machineDirectedLogResidualAtLeastOne_encode]
  by_cases h : 1 ≤ binaryRationalBinaryResidual q
  · simp [h, RawRat.logResidualLower]
  · rw [show decide (1 ≤ binaryRationalBinaryResidual q) = false by simp [h]]
    simp only [machineIfHead_false, machineRawRatNegCode_encode]
    simp [RawRat.logResidualLower, h]

@[simp] theorem machineDirectedLogResidualUpperCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogResidualUpperCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logResidualUpper q N) := by
  rw [machineDirectedLogResidualUpperCode]
  simp only [machineDirectedLogUnitInput_encode,
    machineDirectedLogUnitLowerRawCode_encode,
    machineDirectedLogUnitUpperRawCode_encode,
    machineDirectedLogResidualAtLeastOne_encode]
  by_cases h : 1 ≤ binaryRationalBinaryResidual q
  · simp [h, RawRat.logResidualUpper]
  · rw [show decide (1 ≤ binaryRationalBinaryResidual q) = false by simp [h]]
    simp only [machineIfHead_false, machineRawRatNegCode_encode]
    simp [RawRat.logResidualUpper, h]

@[simp] theorem machineDirectedLogLowerRawCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogLowerRawCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logLower q N) := by
  rw [machineDirectedLogLowerRawCode]
  simp only [machineDirectedLogIntegerLowerCode_encode,
    machineDirectedLogResidualLowerCode_encode,
    machineRawRatAddCode_encode, RawRat.logLower]

@[simp] theorem machineDirectedLogUpperRawCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogUpperRawCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rawRatBinaryCode (RawRat.logUpper q N) := by
  rw [machineDirectedLogUpperRawCode]
  simp only [machineDirectedLogIntegerUpperCode_encode,
    machineDirectedLogResidualUpperCode_encode,
    machineRawRatAddCode_encode, RawRat.logUpper]

theorem machineDirectedLogLowerCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogLowerCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rationalBinaryCode (binaryDirectedLogLower q N) := by
  rw [machineDirectedLogLowerCode,
    machineDirectedLogLowerRawCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_logLower]

theorem machineDirectedLogUpperCode_encode (q : ℚ) (N : ℕ) :
    machineDirectedLogUpperCode
        (pair (List.replicate N true) (rawRatBinaryCode (rawRatOfRat q))) =
      rationalBinaryCode (binaryDirectedLogUpper q N) := by
  rw [machineDirectedLogUpperCode,
    machineDirectedLogUpperRawCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, RawRat.value_logUpper]

end BeyondBethe
