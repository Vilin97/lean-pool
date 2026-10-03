/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRowComplementUpperSum

/-!
# One directed transfer-cost endpoint as a finite-word function

The input is `pair rowUnary (pair columnUnary optimizerWord)`.  The output is
the unreduced rational endpoint `directedTransferCostUpper` at the fixed
certificate precision and regularization scale.  The only row traversal is
the separately verified complement-log upper sum.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary row ruler from a directed transfer-cost request. -/
def machineTransferRowRuler (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the transfer-cost payload following its row ruler. -/
def machineTransferRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extracts the unary column ruler from a directed transfer-cost request. -/
def machineTransferColumnRuler (word : List Bool) : List Bool :=
  machinePairFirst (machineTransferRest word)

/-- Extracts the optimizer input following the requested transfer row and column. -/
def machineTransferOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond (machineTransferRest word)

/-- Reads the encoded matrix from the optimizer input of a transfer-cost request. -/
def machineTransferMatrixWord (word : List Bool) : List Bool :=
  machineOptimizerMatrixWord (machineTransferOptimizerWord word)

/-- Looks up the encoded matrix coefficient at the transfer request's row and column. -/
def machineTransferEntryCode (word : List Bool) : List Bool :=
  machineMatrixEntryAtUnary
    (pair (machineTransferRowRuler word)
      (pair (machineTransferColumnRuler word)
        (machineTransferMatrixWord word)))

/-- Packages the certificate precision, zero reference value, and selected coefficient for
complement evaluation. -/
def machineTransferComplementInput (word : List Bool) : List Bool :=
  pair (machineCertificateLogPrecisionRuler
      (machineTransferOptimizerWord word))
    (pair (rawRatBinaryCode RawRat.zero) (machineTransferEntryCode word))

/-- Computes the encoded complement of the selected transfer coefficient through the
nearby-coordinate complement machine. -/
def machineTransferComplementCode (word : List Bool) : List Bool :=
  machineNearbyCoordinateComplementCode (machineTransferComplementInput word)

/-- Computes the raw scheduled lower logarithm approximation of the selected transfer
coefficient at certificate precision. -/
def machineTransferLogXRawCode (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (pair (machineCertificateLogPrecisionRuler
        (machineTransferOptimizerWord word))
      (machineTransferEntryCode word))

/-- Computes the raw scheduled lower logarithm approximation of the selected coefficient's
complement at certificate precision. -/
def machineTransferLogComplementRawCode (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (pair (machineCertificateLogPrecisionRuler
        (machineTransferOptimizerWord word))
      (machineTransferComplementCode word))

/-- Computes the raw code for one plus the certificate regularization scale. -/
def machineTransferOnePlusTauRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair rawRatOneCode
      (machineCertificateRegularizationScaleRawCode
        (machineTransferOptimizerWord word)))

/-- Multiplies the lower logarithm approximation of the selected coefficient by one plus the
regularization scale. -/
def machineTransferWeightedLogXRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineTransferOnePlusTauRawCode word)
      (machineTransferLogXRawCode word))

/-- Adds the negated weighted coefficient logarithm and negated complement logarithm for the
distinguished transfer entry. -/
def machineTransferNegativeDistinguishedRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineRawRatNegCode (machineTransferWeightedLogXRawCode word))
      (machineRawRatNegCode (machineTransferLogComplementRawCode word)))

/-- Computes the directed upper sum of complement terms along the selected matrix row. -/
def machineTransferRowUpperRawCode (word : List Bool) : List Bool :=
  machineRowComplementUpperSumRawCode
    (pair (machineTransferRowRuler word)
      (machineTransferOptimizerWord word))

/-- Unreduced raw-rational code for one directed transfer cost. -/
def machineDirectedTransferCostUpperRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineTransferNegativeDistinguishedRawCode word)
      (machineTransferRowUpperRawCode word))

theorem machineTransferRowRuler_mem_FP : machineTransferRowRuler ∈ FP :=
  machinePairFirst_mem_FP

theorem machineTransferRest_mem_FP : machineTransferRest ∈ FP :=
  machinePairSecond_mem_FP

theorem machineTransferColumnRuler_mem_FP :
    machineTransferColumnRuler ∈ FP := by
  simpa only [machineTransferColumnRuler] using! machineCompose_mem_FP
    machineTransferRest_mem_FP machinePairFirst_mem_FP

theorem machineTransferOptimizerWord_mem_FP :
    machineTransferOptimizerWord ∈ FP := by
  simpa only [machineTransferOptimizerWord] using! machineCompose_mem_FP
    machineTransferRest_mem_FP machinePairSecond_mem_FP

theorem machineTransferMatrixWord_mem_FP : machineTransferMatrixWord ∈ FP := by
  simpa only [machineTransferMatrixWord] using! machineCompose_mem_FP
    machineTransferOptimizerWord_mem_FP machineOptimizerMatrixWord_mem_FP

theorem machineTransferEntryCode_mem_FP : machineTransferEntryCode ∈ FP := by
  have hinput := machinePair_mem_FP machineTransferRowRuler_mem_FP
    (machinePair_mem_FP machineTransferColumnRuler_mem_FP
      machineTransferMatrixWord_mem_FP)
  simpa only [machineTransferEntryCode] using! machineCompose_mem_FP hinput
    machineMatrixEntryAtUnary_mem_FP

theorem machineTransferComplementInput_mem_FP :
    machineTransferComplementInput ∈ FP := by
  have hp := machineCompose_mem_FP machineTransferOptimizerWord_mem_FP
    machineCertificateLogPrecisionRuler_mem_FP
  exact machinePair_mem_FP hp
    (machinePair_mem_FP (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
      machineTransferEntryCode_mem_FP)

theorem machineTransferComplementCode_mem_FP :
    machineTransferComplementCode ∈ FP := by
  simpa only [machineTransferComplementCode] using! machineCompose_mem_FP
    machineTransferComplementInput_mem_FP
    machineNearbyCoordinateComplementCode_mem_FP

theorem machineTransferLogXRawCode_mem_FP :
    machineTransferLogXRawCode ∈ FP := by
  have hp := machineCompose_mem_FP machineTransferOptimizerWord_mem_FP
    machineCertificateLogPrecisionRuler_mem_FP
  have hinput := machinePair_mem_FP hp machineTransferEntryCode_mem_FP
  simpa only [machineTransferLogXRawCode] using! machineCompose_mem_FP hinput
    machineScheduledLogLowerRawCode_mem_FP

theorem machineTransferLogComplementRawCode_mem_FP :
    machineTransferLogComplementRawCode ∈ FP := by
  have hp := machineCompose_mem_FP machineTransferOptimizerWord_mem_FP
    machineCertificateLogPrecisionRuler_mem_FP
  have hinput := machinePair_mem_FP hp machineTransferComplementCode_mem_FP
  simpa only [machineTransferLogComplementRawCode] using!
    machineCompose_mem_FP hinput machineScheduledLogLowerRawCode_mem_FP

theorem machineTransferOnePlusTauRawCode_mem_FP :
    machineTransferOnePlusTauRawCode ∈ FP := by
  have htau := machineCompose_mem_FP machineTransferOptimizerWord_mem_FP
    machineCertificateRegularizationScaleRawCode_mem_FP
  have hinput := machinePair_mem_FP (machineConst_mem_FP rawRatOneCode) htau
  simpa only [machineTransferOnePlusTauRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineTransferWeightedLogXRawCode_mem_FP :
    machineTransferWeightedLogXRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineTransferOnePlusTauRawCode_mem_FP
    machineTransferLogXRawCode_mem_FP
  simpa only [machineTransferWeightedLogXRawCode] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineTransferNegativeDistinguishedRawCode_mem_FP :
    machineTransferNegativeDistinguishedRawCode ∈ FP := by
  have hfirst := machineCompose_mem_FP
    machineTransferWeightedLogXRawCode_mem_FP machineRawRatNegCode_mem_FP
  have hsecond := machineCompose_mem_FP
    machineTransferLogComplementRawCode_mem_FP machineRawRatNegCode_mem_FP
  have hinput := machinePair_mem_FP hfirst hsecond
  simpa only [machineTransferNegativeDistinguishedRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineTransferRowUpperRawCode_mem_FP :
    machineTransferRowUpperRawCode ∈ FP := by
  have hinput := machinePair_mem_FP machineTransferRowRuler_mem_FP
    machineTransferOptimizerWord_mem_FP
  simpa only [machineTransferRowUpperRawCode] using! machineCompose_mem_FP hinput
    machineRowComplementUpperSumRawCode_mem_FP

theorem machineDirectedTransferCostUpperRawCode_mem_FP :
    machineDirectedTransferCostUpperRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineTransferNegativeDistinguishedRawCode_mem_FP
    machineTransferRowUpperRawCode_mem_FP
  simpa only [machineDirectedTransferCostUpperRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

/-- Forms the raw upper transfer-cost expression from the negated distinguished logarithm terms
and the directed upper complement sum over row `i`. -/
def rawDirectedTransferCostUpper {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) : RawRat :=
  let p := directedCertificatePrecision n
  let tau := rawCertificateRegularizationScale n
  let x := X i j
  (((RawRat.one.add tau).mul (rawScheduledLogLower x p)).neg.add
      (rawScheduledLogLower (1 - x) p).neg).add
    (rawRowComplementUpperSum p RawRat.zero (List.ofFn (X i)))

@[simp] theorem machineTransferEntryCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferEntryCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rationalEntryBinaryCode (X i j) := by
  simp [machineTransferEntryCode, machineTransferRowRuler,
    machineTransferColumnRuler, machineTransferRest,
    machineTransferMatrixWord, machineTransferOptimizerWord]

@[simp] theorem machineTransferComplementCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferComplementCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode (rawRatOfRat (1 - X i j)) := by
  rw [machineTransferComplementCode, machineTransferComplementInput]
  simp only [machineTransferOptimizerWord, machineTransferRest,
    machinePairSecond_pair, machineCertificateLogPrecisionRuler_encode,
    machineTransferEntryCode_encode,
    machineNearbyCoordinateComplementCode_encode]

@[simp] theorem machineTransferLogXRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferLogXRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode
        (rawScheduledLogLower (X i j) (directedCertificatePrecision n)) := by
  rw [machineTransferLogXRawCode]
  simp only [machineTransferOptimizerWord, machineTransferRest,
    machinePairSecond_pair, machineCertificateLogPrecisionRuler_encode,
    machineTransferEntryCode_encode, ← rawRatBinaryCode_rawRatOfRat,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineTransferLogComplementRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferLogComplementRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode
        (rawScheduledLogLower (1 - X i j)
          (directedCertificatePrecision n)) := by
  rw [machineTransferLogComplementRawCode]
  simp only [machineTransferOptimizerWord, machineTransferRest,
    machinePairSecond_pair, machineCertificateLogPrecisionRuler_encode,
    machineTransferComplementCode_encode,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineTransferOnePlusTauRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferOnePlusTauRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode
        (RawRat.one.add (rawCertificateRegularizationScale n)) := by
  rw [machineTransferOnePlusTauRawCode]
  simp only [machineTransferOptimizerWord, machineTransferRest,
    machinePairSecond_pair,
    machineCertificateRegularizationScaleRawCode_encode, rawRatOneCode,
    machineRawRatAddCode_encode]

@[simp] theorem machineTransferRowUpperRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineTransferRowUpperRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode
        (rawRowComplementUpperSum (directedCertificatePrecision n)
          RawRat.zero (List.ofFn (X i))) := by
  simp [machineTransferRowUpperRawCode, machineTransferRowRuler,
    machineTransferOptimizerWord, machineTransferRest]

@[simp] theorem machineDirectedTransferCostUpperRawCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) (i j : Fin n) :
    machineDirectedTransferCostUpperRawCode
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalOptimizerOutputCode ⟨X, R, C⟩))) =
      rawRatBinaryCode (rawDirectedTransferCostUpper X i j) := by
  rw [machineDirectedTransferCostUpperRawCode,
    machineTransferNegativeDistinguishedRawCode,
    machineTransferWeightedLogXRawCode,
    machineTransferOnePlusTauRawCode_encode,
    machineTransferLogXRawCode_encode, machineRawRatMulCode_encode,
    machineRawRatNegCode_encode,
    machineTransferLogComplementRawCode_encode,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode,
    machineTransferRowUpperRawCode_encode, machineRawRatAddCode_encode]
  rfl

theorem rawDirectedTransferCostUpper_value {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (rawDirectedTransferCostUpper X i j).value =
      directedTransferCostUpper (explicitRegularizationScale n) X i j
        (directedCertificatePrecision n) := by
  rw [rawDirectedTransferCostUpper, directedTransferCostUpper,
    RawRat.value_add, RawRat.value_add, RawRat.value_neg,
    RawRat.value_neg, RawRat.value_mul, RawRat.value_add,
    RawRat.value_one, rawCertificateRegularizationScale_value,
    rawScheduledLogLower_value, rawScheduledLogLower_value,
    rawRowComplementUpperSum_matrix_value]
  ring

end BeyondBethe
