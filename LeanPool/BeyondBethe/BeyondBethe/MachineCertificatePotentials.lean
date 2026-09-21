/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorSum

/-!
# Finite-word access and summation for certificate potentials

This is the first component of the directed certificate evaluator.  It parses
the canonical optimizer-output word and forms the unreduced rational sum of
all row and column potentials.
-/

namespace BeyondBethe

open Complexity

def machineOptimizerMatrixWord (word : List Bool) : List Bool :=
  machinePairFirst word

def machineOptimizerPotentialsWord (word : List Bool) : List Bool :=
  machinePairSecond word

def machineOptimizerRowPotentialWord (word : List Bool) : List Bool :=
  machinePairFirst (machineOptimizerPotentialsWord word)

def machineOptimizerColumnPotentialWord (word : List Bool) : List Bool :=
  machinePairSecond (machineOptimizerPotentialsWord word)

theorem machineOptimizerMatrixWord_mem_FP :
    machineOptimizerMatrixWord ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineOptimizerPotentialsWord_mem_FP :
    machineOptimizerPotentialsWord ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineOptimizerRowPotentialWord_mem_FP :
    machineOptimizerRowPotentialWord ∈ Complexity.FP := by
  simpa only [machineOptimizerRowPotentialWord] using
    machineCompose_mem_FP machineOptimizerPotentialsWord_mem_FP
      machinePairFirst_mem_FP

theorem machineOptimizerColumnPotentialWord_mem_FP :
    machineOptimizerColumnPotentialWord ∈ Complexity.FP := by
  simpa only [machineOptimizerColumnPotentialWord] using
    machineCompose_mem_FP machineOptimizerPotentialsWord_mem_FP
      machinePairSecond_mem_FP

@[simp] theorem machineOptimizerMatrixWord_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineOptimizerMatrixWord
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rationalMatrixBinaryEncoding.encode ⟨n, X⟩ := by
  simp [machineOptimizerMatrixWord, rationalOptimizerOutputCode]

@[simp] theorem machineOptimizerRowPotentialWord_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineOptimizerRowPotentialWord
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rationalVectorBinaryCode R := by
  simp [machineOptimizerRowPotentialWord, machineOptimizerPotentialsWord,
    rationalOptimizerOutputCode]

@[simp] theorem machineOptimizerColumnPotentialWord_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineOptimizerColumnPotentialWord
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rationalVectorBinaryCode C := by
  simp [machineOptimizerColumnPotentialWord, machineOptimizerPotentialsWord,
    rationalOptimizerOutputCode]

def machineCertificateRowPotentialRawSumCode
    (word : List Bool) : List Bool :=
  machineRationalVectorRawSumCode
    (machineOptimizerRowPotentialWord word)

def machineCertificateColumnPotentialRawSumCode
    (word : List Bool) : List Bool :=
  machineRationalVectorRawSumCode
    (machineOptimizerColumnPotentialWord word)

def machineCertificatePotentialRawSumCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineCertificateRowPotentialRawSumCode word)
      (machineCertificateColumnPotentialRawSumCode word))

theorem machineCertificateRowPotentialRawSumCode_mem_FP :
    machineCertificateRowPotentialRawSumCode ∈ Complexity.FP := by
  simpa only [machineCertificateRowPotentialRawSumCode] using
    machineCompose_mem_FP machineOptimizerRowPotentialWord_mem_FP
      machineRationalVectorRawSumCode_mem_FP

theorem machineCertificateColumnPotentialRawSumCode_mem_FP :
    machineCertificateColumnPotentialRawSumCode ∈ Complexity.FP := by
  simpa only [machineCertificateColumnPotentialRawSumCode] using
    machineCompose_mem_FP machineOptimizerColumnPotentialWord_mem_FP
      machineRationalVectorRawSumCode_mem_FP

theorem machineCertificatePotentialRawSumCode_mem_FP :
    machineCertificatePotentialRawSumCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineCertificateRowPotentialRawSumCode_mem_FP
    machineCertificateColumnPotentialRawSumCode_mem_FP
  simpa only [machineCertificatePotentialRawSumCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

def rawCertificatePotentialSum {n : ℕ}
    (R C : Fin n → ℚ) : RawRat :=
  (rawRatListSum RawRat.zero (List.ofFn R)).add
    (rawRatListSum RawRat.zero (List.ofFn C))

@[simp] theorem machineCertificatePotentialRawSumCode_encode {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    machineCertificatePotentialRawSumCode
        (rationalOptimizerOutputCode ⟨X, R, C⟩) =
      rawRatBinaryCode (rawCertificatePotentialSum R C) := by
  simp only [machineCertificatePotentialRawSumCode,
    machineCertificateRowPotentialRawSumCode,
    machineCertificateColumnPotentialRawSumCode,
    machineOptimizerRowPotentialWord_encode,
    machineOptimizerColumnPotentialWord_encode,
    machineRationalVectorRawSumCode_encode,
    machineRawRatAddCode_encode, rawCertificatePotentialSum]

theorem rawCertificatePotentialSum_value {n : ℕ}
    (R C : Fin n → ℚ) :
    (rawCertificatePotentialSum R C).value =
      (∑ i, R i) + ∑ j, C j := by
  rw [rawCertificatePotentialSum, RawRat.value_add,
    rawRatListSum_ofFn_value, rawRatListSum_ofFn_value]

end BeyondBethe
