/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExecutableCertificateMagnitude
import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateExpGuard
import LeanPool.BeyondBethe.BeyondBethe.MachineExecutableScannedOptimizerOutput
import LeanPool.BeyondBethe.BeyondBethe.MachineMatchingGain

/-!
# The certificate evaluator for the executable row-major optimizer

The arithmetic transducer is the same verified directed-certificate machine
used elsewhere.  This file proves its contract for the concrete row-major
optimizer output, using only the executable optimizer's proved certificate-log
magnitude bound.
-/

namespace BeyondBethe

open Complexity

theorem executableOptimizerCertificate_expApproxSteps_le_sourceBound
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (executableScannedBetheOptimizerMatrix (m := m + 1) B)
            (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
            (executableScannedBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      explicitCertificateExpStepBound
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩).length := by
  exact certificate_expApproxSteps_le_sourceBound_of_abs_le m B _
    (executableOptimizerCertificateLog_abs_le m B hBpos hBupper)

theorem machineExecutableOptimizerCertificateExpGuard_fits
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (executableScannedBetheOptimizerMatrix (m := m + 1) B)
            (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
            (executableScannedBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      (machineOptimizerCertificateExpGuard
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
          (rationalOptimizerOutputCode
            (executableLargeOptimizerOutput m B)))).length := by
  let source := rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩
  have hsource : 2 ≤ source.length :=
    (show 2 ≤ m + 2 by omega).trans (matrix_dimension_le_code_length B)
  exact
    (executableOptimizerCertificate_expApproxSteps_le_sourceBound
      m B hBpos hBupper).trans
      (by simpa only [machineOptimizerCertificateExpGuard,
        machineCertificateSourceWord_pair,
        machineIteratedBinaryWidth_length, source] using
          explicitCertificateExpStepBound_le_guardWidth hsource)

/-- Correctness of a raw certificate transducer on the concrete outputs of
the executable row-major optimizer. -/
def ExecutableCertificateEvaluatorStringRealizesOnPositiveNormalized
    (F : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ),
    (∀ i j, 0 < B i j) → (∀ i j, B i j ≤ 1) →
    F (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
        (rationalOptimizerOutputCode (executableLargeOptimizerOutput m B))) =
      rawRatBinaryCode
        (rawRatOfRat
          (explicitDirectedCertificateValue
            (executableScannedBetheOptimizerMatrix (m := m + 1) B)
            (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
            (executableScannedBetheOptimizerColumnPotential (m := m + 1) B)))

def machineExecutableCertificateValueRawCode : List Bool → List Bool :=
  machineCertificateValueRawCode machineExplicitMatchingGainRawCode
    machineOptimizerCertificateExpGuard

theorem machineExecutableCertificateValueRawCode_mem_FP :
    machineExecutableCertificateValueRawCode ∈ FP := by
  simpa only [machineExecutableCertificateValueRawCode] using
    machineCertificateValueRawCode_mem_FP
      machineExplicitMatchingGainRawCode_mem_FP
      machineOptimizerCertificateExpGuard_mem_FP

theorem machineExecutableCertificateValueRawCode_realizes_onPositive :
    ExecutableCertificateEvaluatorStringRealizesOnPositiveNormalized
      machineExecutableCertificateValueRawCode := by
  intro m B hBpos hBupper
  simpa only [machineExecutableCertificateValueRawCode,
    executableLargeOptimizerOutput, executableScannedOptimizerOutput,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    machineCertificateValueRawCode_encode
      (gainMachine := machineExplicitMatchingGainRawCode)
      (guardMachine := machineOptimizerCertificateExpGuard)
      (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
      (executableScannedBetheOptimizerMatrix (m := m + 1) B)
      (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
      (executableScannedBetheOptimizerColumnPotential (m := m + 1) B)
      (machineExplicitMatchingGainRawCode_encode
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
        (executableScannedBetheOptimizerMatrix (m := m + 1) B)
        (executableScannedBetheOptimizerRowPotential (m := m + 1) B)
        (executableScannedBetheOptimizerColumnPotential (m := m + 1) B))
      (machineExecutableOptimizerCertificateExpGuard_fits
        m B hBpos hBupper)

end BeyondBethe
