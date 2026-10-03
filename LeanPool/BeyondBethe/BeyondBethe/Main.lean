/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitPositiveRoutine
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitScales
public import LeanPool.BeyondBethe.BeyondBethe.SourceAnariRezaeiList
public import LeanPool.BeyondBethe.BeyondBethe.SourceStableReindex
public import LeanPool.BeyondBethe.BeyondBethe.MachineCompletedAlgorithm
public import LeanPool.BeyondBethe.BeyondBethe.MachinePositiveAlgorithm
public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerCertificateBoundary
public import LeanPool.BeyondBethe.BeyondBethe.MachineExplicitCertificate
public import LeanPool.BeyondBethe.BeyondBethe.ExecutablePositiveRoutine
public import LeanPool.BeyondBethe.BeyondBethe.MachineExecutablePositiveAlgorithm

/-! # Main -/

@[expose] public section

namespace BeyondBethe

/-- A faithful algorithmic statement of Theorem 1 contains both the
two-sided approximation guarantee and a concrete Turing-machine
polynomial-time claim. -/
structure TheoremOneSpec where
  /-- The approximation base, certified positive and strictly below `sqrt 2` by `guarantee`. -/
  c : ℝ
  /-- The dimension-uniform rational matrix algorithm whose output approximates the permanent
  within the certified factor `c^n`. -/
  alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ
  guarantee : ApproximationGuarantee alg c
  polynomialTime : RunsInPolynomialTime alg

/-- The internally reconstructed source theorems imply the exact
positive-matrix certificate used by the numerical layer. -/
theorem exists_exactPositiveCertificate :
    ∃ ε : ℝ, 0 < ε ∧ ExactPositiveCertificate ε := by
  simpa only [ExactPositiveCertificate] using
    exists_absolute_positiveMatrix_logApproximation
      anariOveisGharanStableCoefficient

/-- The one fixed rational algorithm used in the final theorem. -/
def explicitTheoremOneAlgorithm :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ :=
  completedAlgorithm explicitCertifiedPositiveRoutine
    (canonicalSmoothingParameter explicitCertifiedEpsilon)

theorem explicitCertifiedEpsilon_le_quarter :
    explicitCertifiedEpsilon ≤ (1 / 4 : ℚ) := by
  rw [explicitCertifiedEpsilon, explicitCertifiedEpsilon_eq]
  have hδ : explicitDelta ≤ (1 / 200000 : ℚ) := by
    have hcast := explicitDelta_le_rowRatio
    have hcast' : (explicitDelta : ℝ) ≤ ((1 / 200000 : ℚ) : ℝ) := by
      norm_num [explicitRowRatio] at hcast ⊢
      exact hcast
    exact Rat.cast_le.mp hcast'
  calc
    explicitDelta - explicitXi ≤ explicitDelta :=
      sub_le_self _ explicitXi_pos.le
    _ ≤ 1 / 200000 := hδ
    _ ≤ 1 / 4 := by norm_num

/-- The mathematical approximation guarantee of the fixed algorithm is
unconditional; no numerical-oracle interface remains in this statement. -/
theorem explicitTheoremOneAlgorithm_guarantee :
    ApproximationGuarantee explicitTheoremOneAlgorithm
      (finalBase (explicitCertifiedEpsilon : ℝ)) := by
  have hεq : 0 < explicitCertifiedEpsilon := explicitCertifiedEpsilon_pos
  have hε : 0 < (explicitCertifiedEpsilon : ℝ) := by
    exact_mod_cast hεq
  have hquarter : (explicitCertifiedEpsilon : ℝ) ≤ 1 / 4 := by
    have hcast : (explicitCertifiedEpsilon : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by
      exact_mod_cast explicitCertifiedEpsilon_le_quarter
    norm_num at hcast ⊢
    exact hcast
  have hεbound : (explicitCertifiedEpsilon : ℝ) ≤ Real.log 2 / 2 := by
    nlinarith [Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)]
  refine ⟨finalBase_pos _, finalBase_lt_sqrtTwo hε, ?_⟩
  simpa only [explicitTheoremOneAlgorithm] using
    completedAlgorithm_guarantee hε hεbound
      explicitCertifiedPositiveRoutine
      (canonicalSmoothingParameter explicitCertifiedEpsilon)
      (canonicalSmoothingParameter_pos hεq)
      (canonicalSmoothingParameter_le_half hεq)

theorem explicitTheoremOneAlgorithm_runsInPolynomialTime_of_rawPositiveMachine
    {positiveMachine : List Bool → List Bool}
    (hpositiveFP : positiveMachine ∈ Complexity.FP)
    (hrealizes : RawStringRealizes positiveMachine
      explicitCertifiedPositiveRoutine.alg) :
    RunsInPolynomialTime explicitTheoremOneAlgorithm := by
  simpa only [explicitTheoremOneAlgorithm] using
    completedAlgorithm_runsInPolynomialTime_of_rawMachine
      explicitCertifiedPositiveRoutine hpositiveFP hrealizes
      (canonicalSmoothingParameter explicitCertifiedEpsilon)

theorem explicitTheoremOneAlgorithm_runsInPolynomialTime_of_positive_rawMachine
    {positiveMachine : List Bool → List Bool}
    (hpositiveFP : positiveMachine ∈ Complexity.FP)
    (hrealizes : PositiveRawStringRealizes positiveMachine
      explicitCertifiedPositiveRoutine.alg) :
    RunsInPolynomialTime explicitTheoremOneAlgorithm := by
  simpa only [explicitTheoremOneAlgorithm] using
    completedAlgorithm_runsInPolynomialTime_of_positive_rawMachine
      explicitCertifiedPositiveRoutine hpositiveFP hrealizes
      (canonicalSmoothingParameter explicitCertifiedEpsilon)
      (canonicalSmoothingParameter_pos explicitCertifiedEpsilon_pos)

/-- Compatibility statement for the earlier semantic optimizer: a raw-machine
proof for that particular tie-breaking choice still yields Theorem 1. -/
theorem theoremOne_of_explicitPolynomialTime
    (polynomialTime : RunsInPolynomialTime explicitTheoremOneAlgorithm) :
    Nonempty TheoremOneSpec := by
  exact ⟨
    { c := finalBase (explicitCertifiedEpsilon : ℝ)
      alg := explicitTheoremOneAlgorithm
      guarantee := explicitTheoremOneAlgorithm_guarantee
      polynomialTime := polynomialTime }⟩

theorem theoremOne_of_normalizedCertificateMachine
    {certificateMachine : List Bool → List Bool}
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hrealizes : RawStringRealizes certificateMachine
      explicitNormalizedCertificateAlgorithm) :
    Nonempty TheoremOneSpec := by
  let positiveMachine := machinePositiveAlgorithmRawCode certificateMachine
  have hpositiveFP : positiveMachine ∈ Complexity.FP :=
    machinePositiveAlgorithmRawCode_mem_FP hcertificateFP
  have hpositiveRealizes :
      RawStringRealizes positiveMachine explicitPositiveAlgorithm :=
    machinePositiveAlgorithmRawCode_realizes hrealizes
  exact theoremOne_of_explicitPolynomialTime
    (explicitTheoremOneAlgorithm_runsInPolynomialTime_of_rawPositiveMachine
      hpositiveFP hpositiveRealizes)

theorem theoremOne_of_normalizedCertificateMachine_onPositive
    {certificateMachine : List Bool → List Bool}
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hrealizes :
      NormalizedCertificateStringRealizesOnPositive certificateMachine) :
    Nonempty TheoremOneSpec := by
  let positiveMachine := machinePositiveAlgorithmRawCode certificateMachine
  have hpositiveFP : positiveMachine ∈ Complexity.FP :=
    machinePositiveAlgorithmRawCode_mem_FP hcertificateFP
  have hpositiveRealizes :
      PositiveRawStringRealizes positiveMachine explicitPositiveAlgorithm :=
    machinePositiveAlgorithmRawCode_realizes_onPositive hrealizes
  exact theoremOne_of_explicitPolynomialTime
    (explicitTheoremOneAlgorithm_runsInPolynomialTime_of_positive_rawMachine
      hpositiveFP hpositiveRealizes)

/-- Machine-checked Theorem 1 from separate finite-word implementations of
the normalized optimizer and the directed certificate evaluator. -/
theorem theoremOne_of_optimizer_and_certificate_machines
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizerFP : optimizerMachine ∈ Complexity.FP)
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine)
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hcertificate : CertificateEvaluatorStringRealizes certificateMachine) :
    Nonempty TheoremOneSpec := by
  let normalizedMachine := machineNormalizedCertificateFromParts
    optimizerMachine certificateMachine
  have hnormalizedFP : normalizedMachine ∈ Complexity.FP :=
    machineNormalizedCertificateFromParts_mem_FP
      hoptimizerFP hcertificateFP
  have hnormalizedRealizes : RawStringRealizes normalizedMachine
      explicitNormalizedCertificateAlgorithm :=
    machineNormalizedCertificateFromParts_realizes
      hoptimizer hcertificate
  exact theoremOne_of_normalizedCertificateMachine
    hnormalizedFP hnormalizedRealizes

/-- Machine-checked Theorem 1 from machines whose certificate contract is
restricted to the positive normalized inputs used by the algorithm. -/
theorem theoremOne_of_optimizer_and_certificate_machines_onPositive
    {optimizerMachine certificateMachine : List Bool → List Bool}
    (hoptimizerFP : optimizerMachine ∈ Complexity.FP)
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine)
    (hcertificateFP : certificateMachine ∈ Complexity.FP)
    (hcertificate :
      CertificateEvaluatorStringRealizesOnPositiveNormalized certificateMachine) :
    Nonempty TheoremOneSpec := by
  let normalizedMachine := machineNormalizedCertificateFromParts
    optimizerMachine certificateMachine
  have hnormalizedFP : normalizedMachine ∈ Complexity.FP :=
    machineNormalizedCertificateFromParts_mem_FP
      hoptimizerFP hcertificateFP
  have hnormalizedRealizes :
      NormalizedCertificateStringRealizesOnPositive normalizedMachine :=
    machineNormalizedCertificateFromParts_realizes_onPositive
      hoptimizer hcertificate
  exact theoremOne_of_normalizedCertificateMachine_onPositive
    hnormalizedFP hnormalizedRealizes

/-- Legacy modular assembly theorem for replacing the semantic optimizer by
any finite-word implementation satisfying the older exact-output contract. -/
theorem theoremOne_of_optimizerMachine
    {optimizerMachine : List Bool → List Bool}
    (hoptimizerFP : optimizerMachine ∈ Complexity.FP)
    (hoptimizer : LargeOptimizerStringRealizes optimizerMachine) :
    Nonempty TheoremOneSpec := by
  exact theoremOne_of_optimizer_and_certificate_machines_onPositive
    hoptimizerFP hoptimizer
    machineExplicitCertificateValueRawCode_mem_FP
    machineExplicitCertificateValueRawCode_realizes_onPositive

/-! ## Unconditional executable Theorem 1 -/

/-- The completed rational algorithm using the verified row-major optimizer. -/
def executableTheoremOneAlgorithm :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ :=
  completedAlgorithm executableCertifiedPositiveRoutine
    (canonicalSmoothingParameter explicitCertifiedEpsilon)

theorem executableTheoremOneAlgorithm_guarantee :
    ApproximationGuarantee executableTheoremOneAlgorithm
      (finalBase (explicitCertifiedEpsilon : ℝ)) := by
  have hεq : 0 < explicitCertifiedEpsilon := explicitCertifiedEpsilon_pos
  have hε : 0 < (explicitCertifiedEpsilon : ℝ) := by
    exact_mod_cast hεq
  have hεbound : (explicitCertifiedEpsilon : ℝ) ≤ Real.log 2 / 2 := by
    have hquarter : (explicitCertifiedEpsilon : ℝ) ≤ 1 / 4 := by
      have hcast : (explicitCertifiedEpsilon : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by
        exact_mod_cast explicitCertifiedEpsilon_le_quarter
      norm_num at hcast ⊢
      exact hcast
    nlinarith [Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)]
  refine ⟨finalBase_pos _, finalBase_lt_sqrtTwo hε, ?_⟩
  simpa only [executableTheoremOneAlgorithm] using
    completedAlgorithm_guarantee hε hεbound
      executableCertifiedPositiveRoutine
      (canonicalSmoothingParameter explicitCertifiedEpsilon)
      (canonicalSmoothingParameter_pos hεq)
      (canonicalSmoothingParameter_le_half hεq)

theorem executableTheoremOneAlgorithm_runsInPolynomialTime :
    RunsInPolynomialTime executableTheoremOneAlgorithm := by
  simpa only [executableTheoremOneAlgorithm] using
    completedAlgorithm_runsInPolynomialTime_of_positive_rawMachine
      executableCertifiedPositiveRoutine
      machineExecutablePositiveAlgorithmRawCode_mem_FP
      machineExecutablePositiveAlgorithmRawCode_realizes_onPositive
      (canonicalSmoothingParameter explicitCertifiedEpsilon)
      (canonicalSmoothingParameter_pos explicitCertifiedEpsilon_pos)

/-- Fully machine-checked Theorem 1.  Both the approximation guarantee and the
ordinary finite-word polynomial-time implementation are constructed here. -/
theorem theoremOne : Nonempty TheoremOneSpec := by
  exact ⟨
    { c := finalBase (explicitCertifiedEpsilon : ℝ)
      alg := executableTheoremOneAlgorithm
      guarantee := executableTheoremOneAlgorithm_guarantee
      polynomialTime := executableTheoremOneAlgorithm_runsInPolynomialTime }⟩

end BeyondBethe
