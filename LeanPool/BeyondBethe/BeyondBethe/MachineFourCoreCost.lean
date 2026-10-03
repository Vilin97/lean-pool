/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedTransferCost

/-!
# The four-core directed cost as a finite-word function

The input is
`pair rUnary (pair sUnary (pair aUnary (pair bUnary optimizerWord)))`.
The output is the unreduced rational sum of the four directed transfer-cost
endpoints used by the executable row-pair certificate.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary first-row index from a four-core cost query. -/
def machineFourCoreFirstRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the four-core query payload following the first-row index. -/
def machineFourCoreRest₁ (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extracts the unary second-row index from a four-core cost query. -/
def machineFourCoreSecondRowRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₁ word)

/-- Extracts the four-core query payload following both row indices. -/
def machineFourCoreRest₂ (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₁ word)

/-- Extracts the unary first-column index from a four-core cost query. -/
def machineFourCoreFirstColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₂ word)

/-- Extracts the four-core query payload following the first-column index. -/
def machineFourCoreRest₃ (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₂ word)

/-- Extracts the unary second-column index from a four-core cost query. -/
def machineFourCoreSecondColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineFourCoreRest₃ word)

/-- Extracts the optimizer matrix and potentials from the four-core query. -/
def machineFourCoreOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₃ word)

/-- Packages a row index, column index, and optimizer result for transfer-cost evaluation. -/
def machineFourCoreTransferInput
    (row column optimizer : List Bool) : List Bool :=
  pair row (pair column optimizer)

/-- Computes the directed transfer-cost upper approximation at the first row and first column. -/
def machineFourCoreRACostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreFirstRowRuler word)
      (machineFourCoreFirstColumnRuler word)
      (machineFourCoreOptimizerWord word))

/-- Computes the directed transfer-cost upper approximation at the first row and second column. -/
def machineFourCoreRBCostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreFirstRowRuler word)
      (machineFourCoreSecondColumnRuler word)
      (machineFourCoreOptimizerWord word))

/-- Computes the directed transfer-cost upper approximation at the second row and first column. -/
def machineFourCoreSACostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreSecondRowRuler word)
      (machineFourCoreFirstColumnRuler word)
      (machineFourCoreOptimizerWord word))

/-- Computes the directed transfer-cost upper approximation at the second row and second column. -/
def machineFourCoreSBCostRawCode (word : List Bool) : List Bool :=
  machineDirectedTransferCostUpperRawCode
    (machineFourCoreTransferInput
      (machineFourCoreSecondRowRuler word)
      (machineFourCoreSecondColumnRuler word)
      (machineFourCoreOptimizerWord word))

/-- Adds the two directed transfer-cost approximations in the first selected row. -/
def machineFourCoreFirstRowSumRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineFourCoreRACostRawCode word)
      (machineFourCoreRBCostRawCode word))

/-- Adds the two directed transfer-cost approximations in the second selected row. -/
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

/-- Adds the four raw directed transfer-cost approximations at the selected row-column corners. -/
def rawDirectedFourCoreCostUpper {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (r s a b : Fin n) : RawRat :=
  ((rawDirectedTransferCostUpper X r a).add
      (rawDirectedTransferCostUpper X r b)).add
    ((rawDirectedTransferCostUpper X s a).add
      (rawDirectedTransferCostUpper X s b))

/-- Encodes four unary indices together with a matrix and its potentials for four-core
evaluation. -/
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
