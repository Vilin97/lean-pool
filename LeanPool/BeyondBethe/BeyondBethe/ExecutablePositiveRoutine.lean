/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExecutableScannedBetheOptimizer
import LeanPool.BeyondBethe.BeyondBethe.FinalAssembly
import LeanPool.BeyondBethe.BeyondBethe.SourceStableReindex
import Mathlib.Tactic

/-!
# The executable positive-matrix routine

This is the mathematical function computed by the row-major finite-word
optimizer.  Its proof uses the optimizer's proved feasibility and objective
gap, and therefore does not identify its tie-breaking choices with those of
the earlier semantic bisection runner.
-/

namespace BeyondBethe

def executablePositiveAlgorithm :
    ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, A => Matrix.permanent A
  | 1, A => Matrix.permanent A
  | m + 2, A =>
      let B := normalizedRationalMatrix A
      let X := executableScannedBetheOptimizerMatrix (m := m + 1) B
      let R := executableScannedBetheOptimizerRowPotential (m := m + 1) B
      let C := executableScannedBetheOptimizerColumnPotential (m := m + 1) B
      rationalNormalizationScale A ^ (m + 2) *
        explicitDirectedCertificateValue X R C

@[simp] theorem executablePositiveAlgorithm_succ_succ
    (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ) :
    executablePositiveAlgorithm (m + 2) A =
      rationalNormalizationScale A ^ (m + 2) *
        explicitDirectedCertificateValue
          (executableScannedBetheOptimizerMatrix (m := m + 1)
            (normalizedRationalMatrix A))
          (executableScannedBetheOptimizerRowPotential (m := m + 1)
            (normalizedRationalMatrix A))
          (executableScannedBetheOptimizerColumnPotential (m := m + 1)
            (normalizedRationalMatrix A)) := by
  rfl

theorem executablePositiveAlgorithm_succ_succ_spec
    (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hA : Matrix.Positive (fun i j ↦ (A i j : ℝ))) :
    0 < (executablePositiveAlgorithm (m + 2) A : ℝ) ∧
      (executablePositiveAlgorithm (m + 2) A : ℝ) ≤
        ((Matrix.permanent A : ℚ) : ℝ) ∧
      ((Matrix.permanent A : ℚ) : ℝ) ≤
        (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ (m + 2) *
          (executablePositiveAlgorithm (m + 2) A : ℝ) := by
  let B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ :=
    normalizedRationalMatrix A
  let X := executableScannedBetheOptimizerMatrix (m := m + 1) B
  let R := executableScannedBetheOptimizerRowPotential (m := m + 1) B
  let C := executableScannedBetheOptimizerColumnPotential (m := m + 1) B
  let L : ℚ := explicitDirectedCertificateValue X R C
  have hAq : ∀ i j, 0 < A i j := by
    intro i j
    exact positive_rational_of_positive_cast (hA i j)
  have hAnonneg : Matrix.Nonnegative A := fun i j ↦ (hAq i j).le
  have hBpos : ∀ i j, 0 < B i j := by
    intro i j
    change 0 < normalizedRationalMatrix A i j
    rw [normalizedRationalMatrix]
    exact div_pos (hAq i j) (rationalNormalizationScale_pos hAnonneg)
  have hBupper : ∀ i j, B i j ≤ 1 := by
    intro i j
    exact normalizedRationalMatrix_le_one hAnonneg i j
  have hpoint := executableScannedBetheOptimizerPoint_spec (m := m + 1)
    (by omega) B hBpos hBupper
  have hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)) := by
    simpa only [X] using hpoint.2.1
  have hXlo : ∀ i j, (explicitOptimizerFloor B : ℝ) ≤ (X i j : ℝ) := by
    simpa only [X] using hpoint.2.2.1
  have hdelta : 0 < (explicitOptimizerFloor B : ℝ) :=
    Rat.cast_pos.mpr (explicitOptimizerFloor_pos B)
  have hXpos : ∀ i j, 0 < (X i j : ℝ) := by
    intro i j
    exact hdelta.trans_le (hXlo i j)
  have hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)) := by
    intro i
    refine ⟨hX.row_probability i, fun j ↦ ⟨hXpos i j, ?_⟩⟩
    exact hX.entry_lt_one_of_positive hXpos (by simp) i j
  have happrox := executableScannedBetheOptimizer_hasApproximateLogKKT
    (m := m + 1) (by omega) B hBpos hBupper
  have hBR : Matrix.Positive (fun i j ↦ (B i j : ℝ)) := by
    intro i j
    exact Rat.cast_pos.mpr (hBpos i j)
  have hcert := explicitDirectedCertificate_twoSided
    anariOveisGharanStableCoefficient (n := m + 2) (by omega)
    hBR hX hXint (by simpa only [X, R, C, B] using happrox)
  have hLpos : 0 < (L : ℝ) := by
    simpa only [L] using explicitDirectedCertificateValue_pos
      (n := m + 2) (by omega) X R C
  have hscale : 0 < (rationalNormalizationScale A : ℝ) := by
    exact_mod_cast rationalNormalizationScale_pos hAnonneg
  have hper := cast_permanent_eq_scale_pow_mul_normalized A hAnonneg
  have hout :
      (executablePositiveAlgorithm (m + 2) A : ℝ) =
        (rationalNormalizationScale A : ℝ) ^ (m + 2) * (L : ℝ) := by
    simp only [executablePositiveAlgorithm_succ_succ, B, X, R, C, L,
      Rat.cast_mul, Rat.cast_pow]
  have hcert' : (L : ℝ) ≤ Matrix.permanent (fun i j ↦ (B i j : ℝ)) ∧
      Matrix.permanent (fun i j ↦ (B i j : ℝ)) ≤
        (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ (m + 2) *
          (L : ℝ) := by
    simpa only [L, X, R, C] using hcert
  rw [hout]
  refine ⟨mul_pos (pow_pos hscale _) hLpos, ?_, ?_⟩
  · rw [hper]
    exact mul_le_mul_of_nonneg_left hcert'.1 (pow_nonneg hscale.le _)
  · rw [hper]
    have hmul := mul_le_mul_of_nonneg_left hcert'.2
      (pow_nonneg hscale.le (m + 2))
    nlinarith

def executableCertifiedPositiveRoutine :
    CertifiedPositiveRoutine (explicitCertifiedEpsilon : ℝ) where
  alg := executablePositiveAlgorithm
  positiveOutput := by
    intro n hn A hA
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ m =>
        exact (executablePositiveAlgorithm_succ_succ_spec m A hA).1
  lower := by
    intro n hn A hA
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ m =>
        exact (executablePositiveAlgorithm_succ_succ_spec m A hA).2.1
  upper := by
    intro n hn A hA
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ m =>
        exact (executablePositiveAlgorithm_succ_succ_spec m A hA).2.2

end BeyondBethe
