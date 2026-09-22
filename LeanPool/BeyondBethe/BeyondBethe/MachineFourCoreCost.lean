/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedTransferCost

/-!
# The four-core directed cost as a finite-word function

The input is
`pair rUnary (pair sUnary (pair aUnary (pair bUnary optimizerWord)))`.
The output is the unreduced rational sum of the four directed transfer-cost
endpoints used by the executable row-pair certificate.
-/

namespace BeyondBethe

open Complexity

def machineFourCoreFirstRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineFourCoreRest₁ (word : List Bool) : List Bool :=
  machinePairSecond word

def machineFourCoreSecondRowRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₁ word)

def machineFourCoreRest₂ (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₁ word)

def machineFourCoreFirstColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₂ word)

def machineFourCoreRest₃ (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₂ word)

def machineFourCoreSecondColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₃ word)

def machineFourCoreOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₃ word)

def machineFourCoreTransferInput
    (row column optimizer : List Bool) : List Bool :=
  pair row (pair column optimizer)

def machineFourCoreRACostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreFirstRowRuler word)
      (machineFourCoreFirstColumnRuler word)
      (machineFourCoreOptimizerWord word))

def machineFourCoreRBCostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreFirstRowRuler word)
      (machineFourCoreSecondColumnRuler word)
      (machineFourCoreOptimizerWord word))

def machineFourCoreSACostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreSecondRowRuler word)
      (machineFourCoreFirstColumnRuler word)
      (machineFourCoreOptimizerWord word))

def machineFourCoreSBCostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreSecondRowRuler word)
      (machineFourCoreSecondColumnRuler word)
      (machineFourCoreOptimizerWord word))

def machineFourCoreFirstRowSumRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineFourCoreRACostRawCode word)
      (machineFourCoreRBCostRawCode word))

def machineFourCoreSecondRowSumRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineFourCoreSACostRawCode word)
      (machineFourCoreSBCostRawCode word))

/-- Unreduced raw-rational code for the directed four-core cost. -/
def machineDirectedFourCoreCostUpperRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineFourCoreFirstRowSumRawCode word)
      (machineFourCoreSecondRowSumRawCode word))

theorem machineFourCoreFirstRowRuler_mem_FP :
    machineFourCoreFirstRowRuler ∈ FP := machinePairFirst_mem_FP

theorem machineFourCoreRest₁_mem_FP : machineFourCoreRest₁ ∈ FP :=
  machinePairSecond_mem_FP

theorem machineFourCoreSecondRowRuler_mem_FP :
    machineFourCoreSecondRowRuler ∈ FP := by
  simpa only [machineFourCoreSecondRowRuler] using! machineCompose_mem_FP
    machineFourCoreRest₁_mem_FP machinePairFirst_mem_FP

theorem machineFourCoreRest₂_mem_FP : machineFourCoreRest₂ ∈ FP := by
  simpa only [machineFourCoreRest₂] using! machineCompose_mem_FP
    machineFourCoreRest₁_mem_FP machinePairSecond_mem_FP

theorem machineFourCoreFirstColumnRuler_mem_FP :
    machineFourCoreFirstColumnRuler ∈ FP := by
  simpa only [machineFourCoreFirstColumnRuler] using! machineCompose_mem_FP
    machineFourCoreRest₂_mem_FP machinePairFirst_mem_FP

theorem machineFourCoreRest₃_mem_FP : machineFourCoreRest₃ ∈ FP := by
  simpa only [machineFourCoreRest₃] using! machineCompose_mem_FP
    machineFourCoreRest₂_mem_FP machinePairSecond_mem_FP

theorem machineFourCoreSecondColumnRuler_mem_FP :
    machineFourCoreSecondColumnRuler ∈ FP := by
  simpa only [machineFourCoreSecondColumnRuler] using! machineCompose_mem_FP
    machineFourCoreRest₃_mem_FP machinePairFirst_mem_FP

theorem machineFourCoreOptimizerWord_mem_FP :
    machineFourCoreOptimizerWord ∈ FP := by
  simpa only [machineFourCoreOptimizerWord] using! machineCompose_mem_FP
    machineFourCoreRest₃_mem_FP machinePairSecond_mem_FP

theorem machineFourCoreTransferInput_mem_FP
    {row column optimizer : List Bool → List Bool}
    (hrow : row ∈ FP) (hcolumn : column ∈ FP) (hoptimizer : optimizer ∈ FP) :
    (fun word ↦ machineFourCoreTransferInput
      (row word) (column word) (optimizer word)) ∈ FP := by
  exact machinePair_mem_FP hrow (machinePair_mem_FP hcolumn hoptimizer)

theorem machineFourCoreRACostRawCode_mem_FP :
    machineFourCoreRACostRawCode ∈ FP := by
  have hinput := machineFourCoreTransferInput_mem_FP
    machineFourCoreFirstRowRuler_mem_FP machineFourCoreFirstColumnRuler_mem_FP
    machineFourCoreOptimizerWord_mem_FP
  simpa only [machineFourCoreRACostRawCode] using! machineCompose_mem_FP hinput
    machineDirectedTransferCostUpperRawCode_mem_FP

theorem machineFourCoreRBCostRawCode_mem_FP :
    machineFourCoreRBCostRawCode ∈ FP := by
  have hinput := machineFourCoreTransferInput_mem_FP
    machineFourCoreFirstRowRuler_mem_FP machineFourCoreSecondColumnRuler_mem_FP
    machineFourCoreOptimizerWord_mem_FP
  simpa only [machineFourCoreRBCostRawCode] using! machineCompose_mem_FP hinput
    machineDirectedTransferCostUpperRawCode_mem_FP

theorem machineFourCoreSACostRawCode_mem_FP :
    machineFourCoreSACostRawCode ∈ FP := by
  have hinput := machineFourCoreTransferInput_mem_FP
    machineFourCoreSecondRowRuler_mem_FP machineFourCoreFirstColumnRuler_mem_FP
    machineFourCoreOptimizerWord_mem_FP
  simpa only [machineFourCoreSACostRawCode] using! machineCompose_mem_FP hinput
    machineDirectedTransferCostUpperRawCode_mem_FP

theorem machineFourCoreSBCostRawCode_mem_FP :
    machineFourCoreSBCostRawCode ∈ FP := by
  have hinput := machineFourCoreTransferInput_mem_FP
    machineFourCoreSecondRowRuler_mem_FP machineFourCoreSecondColumnRuler_mem_FP
    machineFourCoreOptimizerWord_mem_FP
  simpa only [machineFourCoreSBCostRawCode] using! machineCompose_mem_FP hinput
    machineDirectedTransferCostUpperRawCode_mem_FP

theorem machineFourCoreFirstRowSumRawCode_mem_FP :
    machineFourCoreFirstRowSumRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineFourCoreRACostRawCode_mem_FP
    machineFourCoreRBCostRawCode_mem_FP
  simpa only [machineFourCoreFirstRowSumRawCode] using! machineCompose_mem_FP
    hinput machineRawRatAddCode_mem_FP

theorem machineFourCoreSecondRowSumRawCode_mem_FP :
    machineFourCoreSecondRowSumRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineFourCoreSACostRawCode_mem_FP
    machineFourCoreSBCostRawCode_mem_FP
  simpa only [machineFourCoreSecondRowSumRawCode] using! machineCompose_mem_FP
    hinput machineRawRatAddCode_mem_FP

theorem machineDirectedFourCoreCostUpperRawCode_mem_FP :
    machineDirectedFourCoreCostUpperRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineFourCoreFirstRowSumRawCode_mem_FP
    machineFourCoreSecondRowSumRawCode_mem_FP
  simpa only [machineDirectedFourCoreCostUpperRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

def rawDirectedFourCoreCostUpper {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a b : Fin n) : RawRat :=
  ((rawDirectedTransferCostUpper X r a).add
      (rawDirectedTransferCostUpper X r b)).add
    ((rawDirectedTransferCostUpper X s a).add
      (rawDirectedTransferCostUpper X s b))

def fourCoreMachineInput {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) : List Bool :=
  pair (List.replicate r.1 true)
    (pair (List.replicate s.1 true)
      (pair (List.replicate a.1 true)
        (pair (List.replicate b.1 true)
          (rationalOptimizerOutputCode ⟨X, R, C⟩))))

@[simp] theorem machineFourCoreRACostRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) :
    machineFourCoreRACostRawCode (fourCoreMachineInput X R C r s a b) =
      rawRatBinaryCode (rawDirectedTransferCostUpper X r a) := by
  simp [machineFourCoreRACostRawCode, machineFourCoreTransferInput,
    fourCoreMachineInput, machineFourCoreFirstRowRuler,
    machineFourCoreFirstColumnRuler, machineFourCoreOptimizerWord,
    machineFourCoreRest₁, machineFourCoreRest₂, machineFourCoreRest₃]

@[simp] theorem machineFourCoreRBCostRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) :
    machineFourCoreRBCostRawCode (fourCoreMachineInput X R C r s a b) =
      rawRatBinaryCode (rawDirectedTransferCostUpper X r b) := by
  simp [machineFourCoreRBCostRawCode, machineFourCoreTransferInput,
    fourCoreMachineInput, machineFourCoreFirstRowRuler,
    machineFourCoreSecondColumnRuler, machineFourCoreOptimizerWord,
    machineFourCoreRest₁, machineFourCoreRest₂, machineFourCoreRest₃]

@[simp] theorem machineFourCoreSACostRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) :
    machineFourCoreSACostRawCode (fourCoreMachineInput X R C r s a b) =
      rawRatBinaryCode (rawDirectedTransferCostUpper X s a) := by
  simp [machineFourCoreSACostRawCode, machineFourCoreTransferInput,
    fourCoreMachineInput, machineFourCoreSecondRowRuler,
    machineFourCoreFirstColumnRuler, machineFourCoreOptimizerWord,
    machineFourCoreRest₁, machineFourCoreRest₂, machineFourCoreRest₃]

@[simp] theorem machineFourCoreSBCostRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) :
    machineFourCoreSBCostRawCode (fourCoreMachineInput X R C r s a b) =
      rawRatBinaryCode (rawDirectedTransferCostUpper X s b) := by
  simp [machineFourCoreSBCostRawCode, machineFourCoreTransferInput,
    fourCoreMachineInput, machineFourCoreSecondRowRuler,
    machineFourCoreSecondColumnRuler, machineFourCoreOptimizerWord,
    machineFourCoreRest₁, machineFourCoreRest₂, machineFourCoreRest₃]

@[simp] theorem machineDirectedFourCoreCostUpperRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (r s a b : Fin n) :
    machineDirectedFourCoreCostUpperRawCode
        (fourCoreMachineInput X R C r s a b) =
      rawRatBinaryCode (rawDirectedFourCoreCostUpper X r s a b) := by
  rw [machineDirectedFourCoreCostUpperRawCode,
    machineFourCoreFirstRowSumRawCode, machineFourCoreSecondRowSumRawCode,
    machineFourCoreRACostRawCode_encode, machineFourCoreRBCostRawCode_encode,
    machineRawRatAddCode_encode, machineFourCoreSACostRawCode_encode,
    machineFourCoreSBCostRawCode_encode, machineRawRatAddCode_encode,
    machineRawRatAddCode_encode]
  rfl

theorem rawDirectedFourCoreCostUpper_value {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a b : Fin n) :
    (rawDirectedFourCoreCostUpper X r s a b).value =
      directedFourCoreCostUpper (explicitRegularizationScale n) X r s a b
        (directedPairCostPrecision n) := by
  simp only [rawDirectedFourCoreCostUpper, directedFourCoreCostUpper,
    RawRat.value_add, rawDirectedTransferCostUpper_value,
    directedCertificatePrecision_eq_pairCostPrecision]
  ring

end BeyondBethe
