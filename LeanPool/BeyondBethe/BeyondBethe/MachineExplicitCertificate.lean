/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateExpGuard
public import LeanPool.BeyondBethe.BeyondBethe.MachineMatchingGain

/-!
# The complete finite-word certificate evaluator

This module composes the verified fixed-gain greedy matching transducer, the
directed logarithmic certificate arithmetic, and the polynomial exponential
guard.
-/

@[expose] public section

namespace BeyondBethe

/-- The explicit certificate evaluator using the matching gain and bounded exponential guard. -/
def machineExplicitCertificateValueRawCode : List Bool → List Bool :=
  machineCertificateValueRawCode machineExplicitMatchingGainRawCode
    machineOptimizerCertificateExpGuard

theorem machineExplicitCertificateValueRawCode_mem_FP :
    machineExplicitCertificateValueRawCode ∈ Complexity.FP := by
  simpa only [machineExplicitCertificateValueRawCode] using!
    machineCertificateValueRawCode_mem_FP
      machineExplicitMatchingGainRawCode_mem_FP
      machineOptimizerCertificateExpGuard_mem_FP

theorem machineExplicitCertificateValueRawCode_realizes_onPositive :
    CertificateEvaluatorStringRealizesOnPositiveNormalized
      machineExplicitCertificateValueRawCode := by
  simpa only [machineExplicitCertificateValueRawCode] using!
    machineCertificateValueRawCode_realizes_onPositive
      machineExplicitMatchingGainRawCode_realizes
      machineOptimizerCertificateExpGuard_fits_onPositiveNormalized

end BeyondBethe
