/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachinePositiveAlgorithm
public import LeanPool.BeyondBethe.BeyondBethe.OptimizerOutputEncoding

/-!
# The finite-word interface between optimization and certification

The normalized positive routine has two logically distinct executable parts:
the regularized-Bethe optimizer returns a rational matrix and two rational
potential vectors, and the certificate evaluator consumes exactly those three
objects.  This file fixes their finite-word interface and proves that
polynomial-time machines realizing the two parts compose to a raw-output
machine for `explicitNormalizedCertificateAlgorithm`.

There is deliberately no decoder or noncomputable choice in this interface.
Every well-formed optimizer output is a right-nested word built from the
already fixed matrix and rational-entry encodings.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- The exact optimizer output used by the paper in dimensions at least two. -/
def explicitLargeOptimizerOutput (m : ℕ)
    (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ) :
    RationalOptimizerOutput (m + 2) where
  matrix := explicitBetheOptimizerMatrix (m := m + 1) B
  rowPotential := explicitBetheOptimizerRowPotential (m := m + 1) B
  columnPotential := explicitBetheOptimizerColumnPotential (m := m + 1) B

/-- A raw string function realizes the optimizer on every canonical input of
dimension at least two. -/
def LargeOptimizerStringRealizes (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    F (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩) =
      rationalOptimizerOutputCode (explicitLargeOptimizerOutput m B)

/-- A raw string function realizes the directed certificate evaluator on the
canonical words actually emitted by the fixed optimizer.  Its input retains
the original normalized matrix word as the first component and the optimizer
output as the second.  This source guard is necessary: optimizer potentials
of numerical size `W` can have only `O(log W)` encoded bits, while the final
exponential output can require `Theta(W)` bits. -/
def CertificateEvaluatorStringRealizes
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    F (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
        (rationalOptimizerOutputCode (explicitLargeOptimizerOutput m B))) =
      rawRatBinaryCode
        (rawRatOfRat
          (explicitDirectedCertificateValue
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
          (explicitBetheOptimizerColumnPotential (m := m + 1) B)))

/-- The certificate evaluator is used only on positive matrices whose entries
are at most one.  These are exactly the normalized matrices supplied by the
positive routine.  Requiring correctness outside this domain would impose an
irrelevant numerical-magnitude claim on the totalized optimizer. -/
def CertificateEvaluatorStringRealizesOnPositiveNormalized
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    F (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
        (rationalOptimizerOutputCode (explicitLargeOptimizerOutput m B))) =
      rawRatBinaryCode
        (rawRatOfRat
          (explicitDirectedCertificateValue
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
            (explicitBetheOptimizerColumnPotential (m := m + 1) B)))

/-- Compose optimizer and certificate machines, retaining the exact zero
branches in dimensions zero and one. -/
def machineNormalizedCertificateFromParts
    (optimizerMachine certificateMachine : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineIfHead (machineCompletedDimensionLtTwoBit word)
    (rawRatBinaryCode RawRat.zero)
    (certificateMachine (pair word (optimizerMachine word)))

theorem machineNormalizedCertificateFromParts_mem_FP
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizer : optimizerMachine ∈ Complexity.FP)
    (hcertificate : certificateMachine ∈ Complexity.FP) :
    machineNormalizedCertificateFromParts
      optimizerMachine certificateMachine ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP id_mem_FP hoptimizer
  have hcompose := machineCompose_mem_FP hpair hcertificate
  exact machineIfHead_mem_FP machineCompletedDimensionLtTwoBit_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.zero)) hcompose

theorem machineNormalizedCertificateFromParts_realizes
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine)
    (hcertificate : CertificateEvaluatorStringRealizes certificateMachine) :
    RawStringRealizes
      (machineNormalizedCertificateFromParts
        optimizerMachine certificateMachine)
      explicitNormalizedCertificateAlgorithm := by
  intro x
  obtain ⟨n, B⟩ := x
  rw [machineNormalizedCertificateFromParts,
    machineCompletedDimensionLtTwoBit_encode]
  by_cases hsmall : n < 2
  · rw [show [decide (n < 2)] = [true] by simp [hsmall],
      machineIfHead_true]
    interval_cases n <;> rfl
  · rw [show [decide (n < 2)] = [false] by simp [hsmall],
      machineIfHead_false]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      use n - 2
      omega
    rw [hoptimizer m B]
    exact hcertificate m B

theorem machineNormalizedCertificateFromParts_realizes_onPositive
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine)
    (hcertificate :
      CertificateEvaluatorStringRealizesOnPositiveNormalized certificateMachine) :
    NormalizedCertificateStringRealizesOnPositive
      (machineNormalizedCertificateFromParts
        optimizerMachine certificateMachine) := by
  intro m B hBpos hBupper
  rw [machineNormalizedCertificateFromParts,
    machineCompletedDimensionLtTwoBit_encode,
    show [decide (m + 2 < 2)] = [false] by simp,
    machineIfHead_false, hoptimizer m B]
  exact hcertificate m B hBpos hBupper

theorem normalizedCertificate_rawMachine_of_parts
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizerFP : optimizerMachine ∈ Complexity.FP)
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine)
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hcertificate : CertificateEvaluatorStringRealizes certificateMachine) :
    ∃ F : List Bool → List Bool,
      F ∈ Complexity.FP ∧
      RawStringRealizes F explicitNormalizedCertificateAlgorithm := by
  exact ⟨machineNormalizedCertificateFromParts
      optimizerMachine certificateMachine,
    machineNormalizedCertificateFromParts_mem_FP
      hoptimizerFP hcertificateFP,
    machineNormalizedCertificateFromParts_realizes
      hoptimizer hcertificate⟩

end BeyondBethe
