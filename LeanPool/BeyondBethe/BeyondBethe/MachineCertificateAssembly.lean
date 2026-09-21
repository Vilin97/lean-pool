/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineNearbyMatrixSum
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalExp

/-!
# Assembly of the directed certificate from its matching gain

This module isolates the remaining combinatorial and exponential-size
obligations.  Given a finite-word machine for the fixed greedy matching gain,
it forms the complete rational certificate logarithm.  Given in addition a
unary exponential guard, it returns the final canonical raw rational entry.
All composition and rational-format conversions are explicit.
-/

namespace BeyondBethe

open Complexity

/-- The source matrix word retained by the certificate interface. -/
def machineCertificateSourceWord (word : List Bool) : List Bool :=
  machinePairFirst word

/-- The optimizer-output word consumed by the arithmetic subroutines. -/
def machineCertificateOptimizerWord (word : List Bool) : List Bool :=
  machinePairSecond word

theorem machineCertificateSourceWord_mem_FP :
    machineCertificateSourceWord ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineCertificateOptimizerWord_mem_FP :
    machineCertificateOptimizerWord ∈ Complexity.FP :=
  machinePairSecond_mem_FP

@[simp] theorem machineCertificateSourceWord_pair
    (source optimizer : List Bool) :
    machineCertificateSourceWord (pair source optimizer) = source :=
  machinePairFirst_pair source optimizer

@[simp] theorem machineCertificateOptimizerWord_pair
    (source optimizer : List Bool) :
    machineCertificateOptimizerWord (pair source optimizer) = optimizer :=
  machinePairSecond_pair source optimizer

def rawCertificateLogAssembly {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (gain : ℚ) : RawRat :=
  (((rawCertificatePotentialSum R C).add
      (rawNearbyRowsSum (rawCertificateRegularizationScale n)
        (directedCertificatePrecision n) RawRat.zero
        (rationalMatrixRows X))).add
    (rawRatOfRat gain)).add (rawCertificateKKTPenalty n).neg

theorem rawCertificateLogAssembly_value {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (gain : ℚ) :
    (rawCertificateLogAssembly X R C gain).value =
      directedNearbyBetheLower (explicitRegularizationScale n) X R C
          (directedCertificatePrecision n) +
        gain - explicitKKTError * n := by
  rw [rawCertificateLogAssembly, RawRat.value_add, RawRat.value_add,
    RawRat.value_add, RawRat.value_neg,
    rawCertificatePotentialSum_value,
    rawNearbyRowsSum_certificate_value,
    rawRatOfRat_value, rawCertificateKKTPenalty_value]
  rw [directedNearbyBetheLower]
  ring

def machineCertificateNearbyRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair
      (machineCertificatePotentialRawSumCode
        (machineCertificateOptimizerWord word))
      (machineNearbyMatrixRawSumCode
        (machineCertificateOptimizerWord word)))

def machineCertificateLogBeforePenaltyRawCode
    (gainMachine : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineCertificateNearbyRawCode word) (gainMachine word))

def machineCertificateLogUnnormalizedRawCode
    (gainMachine : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineCertificateLogBeforePenaltyRawCode gainMachine word)
      (machineRawRatNegCode
        (machineCertificateKKTPenaltyRawCode
          (machineCertificateOptimizerWord word))))

/-- Canonical raw-entry encoding of the complete certificate logarithm. -/
def machineCertificateLogRawCode
    (gainMachine : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineCertificateLogUnnormalizedRawCode gainMachine word)

theorem machineCertificateNearbyRawCode_mem_FP :
    machineCertificateNearbyRawCode ∈ Complexity.FP := by
  have hpotential := machineCompose_mem_FP
    machineCertificateOptimizerWord_mem_FP
    machineCertificatePotentialRawSumCode_mem_FP
  have hnearby := machineCompose_mem_FP
    machineCertificateOptimizerWord_mem_FP
    machineNearbyMatrixRawSumCode_mem_FP
  have hpair := machinePair_mem_FP
    hpotential hnearby
  simpa only [machineCertificateNearbyRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineCertificateLogBeforePenaltyRawCode_mem_FP
    {gainMachine : List Bool → List Bool}
    (hgain : gainMachine ∈ Complexity.FP) :
    machineCertificateLogBeforePenaltyRawCode gainMachine ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineCertificateNearbyRawCode_mem_FP hgain
  simpa only [machineCertificateLogBeforePenaltyRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineCertificateLogUnnormalizedRawCode_mem_FP
    {gainMachine : List Bool → List Bool}
    (hgain : gainMachine ∈ Complexity.FP) :
    machineCertificateLogUnnormalizedRawCode gainMachine ∈ Complexity.FP := by
  have hpenalty := machineCompose_mem_FP
    machineCertificateOptimizerWord_mem_FP
    machineCertificateKKTPenaltyRawCode_mem_FP
  have hneg := machineCompose_mem_FP hpenalty machineRawRatNegCode_mem_FP
  have hpair := machinePair_mem_FP
    (machineCertificateLogBeforePenaltyRawCode_mem_FP hgain) hneg
  simpa only [machineCertificateLogUnnormalizedRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineCertificateLogRawCode_mem_FP
    {gainMachine : List Bool → List Bool}
    (hgain : gainMachine ∈ Complexity.FP) :
    machineCertificateLogRawCode gainMachine ∈ Complexity.FP := by
  simpa only [machineCertificateLogRawCode] using
    machineCompose_mem_FP
      (machineCertificateLogUnnormalizedRawCode_mem_FP hgain)
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineCertificateLogUnnormalizedRawCode_encode
    {gainMachine : List Bool → List Bool}
    (source : List Bool)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (hgain : gainMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode (rawRatOfRat (explicitCertifiedMatchingGain X))) :
    machineCertificateLogUnnormalizedRawCode gainMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode
        (rawCertificateLogAssembly X R C
          (explicitCertifiedMatchingGain X)) := by
  rw [machineCertificateLogUnnormalizedRawCode,
    machineCertificateLogBeforePenaltyRawCode,
    machineCertificateNearbyRawCode,
    machineCertificateOptimizerWord_pair,
    machineCertificatePotentialRawSumCode_encode,
    machineNearbyMatrixRawSumCode_encode,
    hgain, machineCertificateKKTPenaltyRawCode_encode,
    machineRawRatNegCode_encode, machineRawRatAddCode_encode,
    machineRawRatAddCode_encode, machineRawRatAddCode_encode]
  rfl

theorem machineCertificateLogRawCode_encode
    {gainMachine : List Bool → List Bool}
    (source : List Bool)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (hgain : gainMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode (rawRatOfRat (explicitCertifiedMatchingGain X))) :
    machineCertificateLogRawCode gainMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode
        (rawRatOfRat (explicitDirectedCertificateLog X R C)) := by
  rw [machineCertificateLogRawCode,
    machineCertificateLogUnnormalizedRawCode_encode
      (gainMachine := gainMachine) source X R C hgain,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value,
    rawCertificateLogAssembly_value,
    explicitDirectedCertificateLog]

def machineCertificateExpInput
    (gainMachine guardMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  pair (guardMachine word)
    (pair (machineCertificateLogRawCode gainMachine word)
      (machineCertificateExpLossRawCode
        (machineCertificateOptimizerWord word)))

def machineCertificateValueRawCode
    (gainMachine guardMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineBoundedRationalExpLowerRawEntryCode
    (machineCertificateExpInput gainMachine guardMachine word)

theorem machineCertificateExpInput_mem_FP
    {gainMachine guardMachine : List Bool → List Bool}
    (hgain : gainMachine ∈ Complexity.FP)
    (hguard : guardMachine ∈ Complexity.FP) :
    machineCertificateExpInput gainMachine guardMachine ∈ Complexity.FP := by
  exact machinePair_mem_FP hguard
    (machinePair_mem_FP (machineCertificateLogRawCode_mem_FP hgain)
      (machineCompose_mem_FP machineCertificateOptimizerWord_mem_FP
        machineCertificateExpLossRawCode_mem_FP))

theorem machineCertificateValueRawCode_mem_FP
    {gainMachine guardMachine : List Bool → List Bool}
    (hgain : gainMachine ∈ Complexity.FP)
    (hguard : guardMachine ∈ Complexity.FP) :
    machineCertificateValueRawCode gainMachine guardMachine ∈ Complexity.FP := by
  simpa only [machineCertificateValueRawCode] using
    machineCompose_mem_FP (machineCertificateExpInput_mem_FP hgain hguard)
      machineBoundedRationalExpLowerRawEntryCode_mem_FP

theorem machineCertificateValueRawCode_encode
    {gainMachine guardMachine : List Bool → List Bool}
    (source : List Bool)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ)
    (hgain : gainMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode (rawRatOfRat (explicitCertifiedMatchingGain X)))
    (hsteps : RawRat.expApproxSteps
      (rawRatOfRat (explicitDirectedCertificateLog X R C))
      (rawCertificateExpLoss n) ≤
        (guardMachine
          (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩))).length) :
    machineCertificateValueRawCode gainMachine guardMachine
        (pair source (rationalOptimizerOutputCode ⟨X, R, C⟩)) =
      rawRatBinaryCode
        (rawRatOfRat (explicitDirectedCertificateValue X R C)) := by
  rw [machineCertificateValueRawCode, machineCertificateExpInput,
    machineCertificateLogRawCode_encode
      (gainMachine := gainMachine) source X R C hgain,
    machineCertificateOptimizerWord_pair,
    machineCertificateExpLossRawCode_encode,
    machineBoundedRationalExpLowerRawEntryCode_encode _ _ _ hsteps,
    rawRatOfRat_value, rawCertificateExpLoss_value,
    binaryRationalExpLower_eq, explicitDirectedCertificateValue]

/-- Correctness required of the remaining fixed-gain matching transducer. -/
def OptimizerMatchingGainStringRealizes
    (gainMachine : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    gainMachine
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
          (rationalOptimizerOutputCode (explicitLargeOptimizerOutput m B))) =
      rawRatBinaryCode
        (rawRatOfRat
          (explicitCertifiedMatchingGain
            (explicitBetheOptimizerMatrix (m := m + 1) B)))

/-- The optimizer-dependent magnitude statement still needed by the guarded
exponential.  It is separated from machine composition so that no universal
claim about arbitrary rational potentials is hidden in the evaluator. -/
def OptimizerCertificateExpGuardFits
    (guardMachine : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
            (explicitBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      (guardMachine
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
          (rationalOptimizerOutputCode
            (explicitLargeOptimizerOutput m B)))).length

/-- The guarded exponential needs to fit only on the positive normalized
matrices on which the certificate theorem and the outer algorithm use it. -/
def OptimizerCertificateExpGuardFitsOnPositiveNormalized
    (guardMachine : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
            (explicitBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      (guardMachine
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
          (rationalOptimizerOutputCode
            (explicitLargeOptimizerOutput m B)))).length

theorem machineCertificateValueRawCode_realizes
    {gainMachine guardMachine : List Bool → List Bool}
    (hgain : OptimizerMatchingGainStringRealizes gainMachine)
    (hguard : OptimizerCertificateExpGuardFits guardMachine) :
    CertificateEvaluatorStringRealizes
      (machineCertificateValueRawCode gainMachine guardMachine) := by
  intro m B
  simpa only [explicitLargeOptimizerOutput] using
    machineCertificateValueRawCode_encode
      (gainMachine := gainMachine) (guardMachine := guardMachine)
      (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
      (explicitBetheOptimizerMatrix (m := m + 1) B)
      (explicitBetheOptimizerRowPotential (m := m + 1) B)
      (explicitBetheOptimizerColumnPotential (m := m + 1) B)
      (hgain m B) (hguard m B)

theorem machineCertificateValueRawCode_realizes_onPositive
    {gainMachine guardMachine : List Bool → List Bool}
    (hgain : OptimizerMatchingGainStringRealizes gainMachine)
    (hguard :
      OptimizerCertificateExpGuardFitsOnPositiveNormalized guardMachine) :
    CertificateEvaluatorStringRealizesOnPositiveNormalized
      (machineCertificateValueRawCode gainMachine guardMachine) := by
  intro m B hBpos hBupper
  simpa only [explicitLargeOptimizerOutput] using
    machineCertificateValueRawCode_encode
      (gainMachine := gainMachine) (guardMachine := guardMachine)
      (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
      (explicitBetheOptimizerMatrix (m := m + 1) B)
      (explicitBetheOptimizerRowPotential (m := m + 1) B)
      (explicitBetheOptimizerColumnPotential (m := m + 1) B)
      (hgain m B) (hguard m B hBpos hBupper)

end BeyondBethe
