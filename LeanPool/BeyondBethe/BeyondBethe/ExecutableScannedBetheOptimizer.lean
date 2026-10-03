/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerBisectionSemantics
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitBetheOptimizer
public import Mathlib.Tactic

/-!
# Correctness of the executable row-major Bethe optimizer

The finite-word optimizer uses the concrete unreduced dyadic floor emitted by
the scale machine and the row-major separation oracle.  This file defines its
mathematical output, proves the same objective-gap specification as the
paper-level optimizer, and derives the approximate logarithmic KKT equations
without identifying its tie-breaking choices with those of any other runner.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- The raw-rational coordinate floor for the scanned optimizer, determined by the dimension and
entry bit bound. -/
def executableScannedBetheOptimizerFloor {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : RawRat :=
  rawExplicitOptimizerFloor (m + 1) (rationalMatrixEntryBitBound A)

/-- Initialize scanned Bethe bisection with the explicit regularization, precision, floor,
mixing weight, and inner radius. -/
def executableScannedBetheOptimizerInitialState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    BetheBisectionState (m * m + 1) :=
  initialScannedBetheBisectionState
    (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A)
    (executableScannedBetheOptimizerFloor A)
    (explicitOptimizerMix A) (explicitOptimizerInnerRadius A)

/-- Run scanned Bethe bisection for the prescribed explicit number of iterations. -/
def executableScannedBetheOptimizerState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    BetheBisectionState (m * m + 1) :=
  runScannedBetheBisection
    (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A)
    (executableScannedBetheOptimizerFloor A)
    (explicitOptimizerInnerRadius A)
    (explicitOptimizerBisectionSteps A)
    (executableScannedBetheOptimizerInitialState A)

/-- The default branch makes the rational algorithm total.  Correctness below
proves that it is never used on positive normalized inputs. -/
def executableScannedBetheOptimizerPoint {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Fin (m * m + 1) → ℚ :=
  (executableScannedBetheOptimizerState A).witness.getD 0

/-- Recover the affine matrix from the epigraph base coordinates of the scanned optimizer point. -/
def executableScannedBetheOptimizerMatrix {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  betheAffineMatrixQ (epigraphBase (executableScannedBetheOptimizerPoint A))

/-- The directed lower negative-gradient matrix evaluated at the scanned optimizer matrix. -/
def executableScannedBetheOptimizerGradient {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  directedNegativeGradientLowerMatrix
    (explicitRegularizationScale (m + 1)) A
    (executableScannedBetheOptimizerMatrix A)
    (explicitOptimizerPrecision A)

/-- The row potential obtained from the negative first-column gradient entry and the
regularization offset. -/
def executableScannedBetheOptimizerRowPotential {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : Fin (m + 1) → ℚ :=
  fun i ↦ -executableScannedBetheOptimizerGradient A i 0 +
    (2 + explicitRegularizationScale (m + 1))

/-- The column potential obtained from the negative first-row gradient difference relative to
column zero. -/
def executableScannedBetheOptimizerColumnPotential {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : Fin (m + 1) → ℚ :=
  fun j ↦ -(executableScannedBetheOptimizerGradient A 0 j -
    executableScannedBetheOptimizerGradient A 0 0)

@[simp] theorem executableScannedBetheOptimizerFloor_value {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    (executableScannedBetheOptimizerFloor A).value =
      explicitOptimizerFloor A := by
  exact (rawExplicitOptimizerScales_value A).1

theorem executableScannedBetheOptimizerPoint_spec {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    BetheEpigraphOracleAccepted (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A) (explicitOptimizerFloor A)
        (executableScannedBetheOptimizerState A).high
        (executableScannedBetheOptimizerPoint A) ∧
      IsDoublyStochastic
        (fun i j ↦ ((executableScannedBetheOptimizerMatrix A i j : ℚ) : ℝ)) ∧
      (∀ i j, (explicitOptimizerFloor A : ℝ) ≤
        (executableScannedBetheOptimizerMatrix A i j : ℝ)) ∧
      ∃ X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        IsDoublyStochastic X ∧
        (∀ Y, IsDoublyStochastic Y →
          regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) Y ≤
            regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) X) ∧
        regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ)) X -
            regularizedBetheObjective
              (explicitRegularizationScale (m + 1) : ℝ)
              (fun i j ↦ (A i j : ℝ))
              (fun i j ↦
                ((executableScannedBetheOptimizerMatrix A i j : ℚ) : ℝ)) ≤
          (explicitOptimizerGap A : ℝ) := by
  let tau : ℚ := explicitRegularizationScale (m + 1)
  let delta := executableScannedBetheOptimizerFloor A
  obtain ⟨X, hX, hmax⟩ := exists_regularizedBetheMaximizer
    (tau : ℝ) (fun i j ↦ (A i j : ℝ))
  have htau0 : 0 < tau := explicitRegularizationScale_pos (by omega)
  have htau1 : tau ≤ 1 := explicitRegularizationScale_le_one (by omega)
  have hdelta : 0 < delta.value := by
    change 0 < (executableScannedBetheOptimizerFloor A).value
    rw [executableScannedBetheOptimizerFloor_value]
    exact explicitOptimizerFloor_pos A
  have hfloor : delta.value ≤ (1 - explicitOptimizerMix A) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) tau := by
    change (executableScannedBetheOptimizerFloor A).value ≤
      (1 - explicitOptimizerMix A) *
        numericalInteriorFloor (m + 1)
          (rationalMatrixEntryBitBound A) tau
    rw [executableScannedBetheOptimizerFloor_value]
    simpa only [tau] using explicitOptimizerFloor_le_smoothedFloor A
  have hrun := runScannedBetheBisection_objective_gap hm htau0 htau1
    hApos hAupper hX hmax
    (explicitOptimizerMix_pos A) (explicitOptimizerMix_le_one A)
    hdelta (explicitOptimizerInnerRadius_pos A)
    (explicitOptimizerInnerRadius_spike A) hfloor
    (explicitOptimizerPrecision A) (explicitOptimizerBisectionSteps A)
  have hrun' : ∃ q : Fin (m * m + 1) → ℚ,
      (executableScannedBetheOptimizerState A).witness = some q ∧
      BetheEpigraphOracleAccepted tau A (explicitOptimizerPrecision A)
        delta.value (executableScannedBetheOptimizerState A).high q ∧
      IsDoublyStochastic (acceptedBetheMatrix q) ∧
      (∀ i j, (delta.value : ℝ) ≤ acceptedBetheMatrix q i j) ∧
      regularizedBetheObjective (tau : ℝ) (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective (tau : ℝ) (fun i j ↦ (A i j : ℝ))
          (acceptedBetheMatrix q) ≤
        (betheSmoothingSlack A (explicitOptimizerMix A)
            (explicitOptimizerInnerRadius A) : ℝ) +
          (explicitOptimizerInitialWidth A /
              2 ^ explicitOptimizerBisectionSteps A : ℚ) +
          (betheObjectiveEvaluationError m
            (explicitOptimizerPrecision A) : ℝ) := by
    simpa only [tau, delta, executableScannedBetheOptimizerState,
      executableScannedBetheOptimizerInitialState,
      explicitOptimizerInitialWidth] using hrun
  obtain ⟨q, hq, haccepted, hqDS, hqfloor, hqgap⟩ := hrun'
  have hpoint : executableScannedBetheOptimizerPoint A = q := by
    rw [executableScannedBetheOptimizerPoint, hq]
    rfl
  have hmatrixCast :
      (fun i j ↦
        ((executableScannedBetheOptimizerMatrix A i j : ℚ) : ℝ)) =
        acceptedBetheMatrix q := by
    ext i j
    rw [executableScannedBetheOptimizerMatrix, hpoint]
    exact cast_betheAffineMatrixQ (epigraphBase q) i j
  have htotalQ := explicitOptimizerTotalObjectiveError_lt A
  have htotal :
      (betheSmoothingSlack A (explicitOptimizerMix A)
            (explicitOptimizerInnerRadius A) : ℝ) +
          (explicitOptimizerInitialWidth A /
              2 ^ explicitOptimizerBisectionSteps A : ℚ) +
          (betheObjectiveEvaluationError m
            (explicitOptimizerPrecision A) : ℝ) <
        (explicitOptimizerGap A : ℝ) := by
    exact_mod_cast htotalQ
  refine ⟨?_, ?_, ?_, X, hX, hmax, ?_⟩
  · simpa only [tau, delta,
      executableScannedBetheOptimizerFloor_value, hpoint] using haccepted
  · simpa only [hmatrixCast] using hqDS
  · intro i j
    change (explicitOptimizerFloor A : ℝ) ≤
      (fun a b ↦
        ((executableScannedBetheOptimizerMatrix A a b : ℚ) : ℝ)) i j
    rw [hmatrixCast]
    simpa only [delta, executableScannedBetheOptimizerFloor_value] using
      hqfloor i j
  · rw [hmatrixCast]
    exact hqgap.trans htotal.le

theorem executableScannedBetheOptimizer_hasApproximateLogKKT
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    HasApproximateLogKKT (explicitKKTError : ℝ)
      (explicitRegularizationScale (m + 1) : ℝ)
      (fun i j ↦ (A i j : ℝ))
      (fun i j ↦
        ((executableScannedBetheOptimizerMatrix A i j : ℚ) : ℝ))
      (fun i ↦ (executableScannedBetheOptimizerRowPotential A i : ℝ))
      (fun j ↦
        (executableScannedBetheOptimizerColumnPotential A j : ℝ)) := by
  obtain ⟨_, hY, hYlo, X, hX, hmax, hgap⟩ :=
    executableScannedBetheOptimizerPoint_spec hm A hApos hAupper
  simpa only [executableScannedBetheOptimizerGradient,
    executableScannedBetheOptimizerRowPotential,
    executableScannedBetheOptimizerColumnPotential] using
    hasApproximateLogKKT_of_explicitOptimizerSpec hm A hApos hAupper
      (executableScannedBetheOptimizerMatrix A) hY hYlo X hX hmax hgap

/-! ## Exact agreement with the finite-word bisection output -/

theorem executableScannedBetheOptimizerState_indexAgrees {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    ScannedOptimizerIndexAgrees A
      (executableScannedBetheOptimizerState A)
      (runScannedOptimizerIndex A (explicitOptimizerBisectionSteps A) 0 0)
      (explicitOptimizerBisectionSteps A) := by
  simpa only [executableScannedBetheOptimizerState,
    executableScannedBetheOptimizerInitialState,
    executableScannedBetheOptimizerFloor, Nat.zero_add] using
    runScannedOptimizerIndex_agrees A
      (initialScannedOptimizerIndexAgrees A)
      (explicitOptimizerBisectionSteps A)

theorem executableScannedBetheOptimizer_witness_eq_some
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    (executableScannedBetheOptimizerState A).witness =
      some (executableScannedBetheOptimizerPoint A) := by
  let tau : ℚ := explicitRegularizationScale (m + 1)
  obtain ⟨X, hX, hmax⟩ := exists_regularizedBetheMaximizer
    (tau : ℝ) (fun i j ↦ (A i j : ℝ))
  have htau0 : 0 < tau := explicitRegularizationScale_pos (by omega)
  have htau1 : tau ≤ 1 := explicitRegularizationScale_le_one (by omega)
  have hdelta : 0 < (executableScannedBetheOptimizerFloor A).value := by
    rw [executableScannedBetheOptimizerFloor_value]
    exact explicitOptimizerFloor_pos A
  have hfloor : (executableScannedBetheOptimizerFloor A).value ≤
      (1 - explicitOptimizerMix A) *
        numericalInteriorFloor (m + 1)
          (rationalMatrixEntryBitBound A) tau := by
    rw [executableScannedBetheOptimizerFloor_value]
    simpa only [tau] using explicitOptimizerFloor_le_smoothedFloor A
  have hsome0 :=
    initialScannedBetheBisectionState_has_witness_of_optimizer
      hm htau0 htau1 hApos hAupper hX hmax
      (explicitOptimizerMix_pos A) (explicitOptimizerMix_le_one A)
      hdelta (explicitOptimizerInnerRadius_pos A)
      (explicitOptimizerInnerRadius_spike A) hfloor
      (explicitOptimizerPrecision A)
  have hsome := runScannedBetheBisection_preserves_some
    tau A (explicitOptimizerPrecision A)
    (executableScannedBetheOptimizerFloor A)
    (explicitOptimizerInnerRadius A) hsome0
    (explicitOptimizerBisectionSteps A)
  obtain ⟨q, hq⟩ := hsome
  have hq' : (executableScannedBetheOptimizerState A).witness = some q := by
    simpa only [tau, executableScannedBetheOptimizerState,
      executableScannedBetheOptimizerInitialState] using hq
  rw [executableScannedBetheOptimizerPoint, hq']
  rfl

theorem executableScannedBetheOptimizer_finalFeasibilityResult
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    runExplicitScannedBetheThresholdFeasibility
        (explicitRegularizationScale (m + 1)) A
        (explicitOptimizerPrecision A)
        (executableScannedBetheOptimizerFloor A)
        (rawRatOfRat (executableScannedBetheOptimizerState A).high)
        (explicitOptimizerInnerRadius A) =
      .accepted (executableScannedBetheOptimizerPoint A) := by
  have hvalid0 := initialScannedBetheBisectionState_witnessValid
    (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A)
    (executableScannedBetheOptimizerFloor A)
    (explicitOptimizerMix A) (explicitOptimizerInnerRadius A)
  have hvalidN := runScannedBetheBisection_witnessValid
    (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A)
    (executableScannedBetheOptimizerFloor A)
    (explicitOptimizerInnerRadius A) hvalid0
    (explicitOptimizerBisectionSteps A)
  exact (hvalidN (executableScannedBetheOptimizerPoint A) (by
    simpa only [executableScannedBetheOptimizerState,
      executableScannedBetheOptimizerInitialState] using
      executableScannedBetheOptimizer_witness_eq_some
        hm A hApos hAupper)).1

@[simp] theorem machineExplicitBetheOptimizerFeasibilityResultCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExplicitBetheOptimizerFeasibilityResultCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalFeasibilityResultBinaryCode
        (.accepted (executableScannedBetheOptimizerPoint A)) := by
  let N := explicitOptimizerBisectionSteps A
  let k := runScannedOptimizerIndex A N 0 0
  have hagree := executableScannedBetheOptimizerState_indexAgrees A
  have hhigh : (executableScannedBetheOptimizerState A).high =
      optimizerDyadicThreshold A (k + 1) N := by
    simpa only [N, k] using hagree.2
  rw [machineExplicitBetheOptimizerFeasibilityResultCode,
    machineOptimizerBisectionFinalState_encode hm A hApos,
    machineOptimizerBisectionHighRawCode_encode]
  rw [← hhigh]
  change machineExplicitBetheThresholdFeasibilityCode
      (optimizerFeasibilityCallCode A
        (rawRatOfRat (executableScannedBetheOptimizerState A).high)) = _
  rw [machineExplicitBetheThresholdFeasibilityCode_encode hm A hApos]
  apply congrArg rationalFeasibilityResultBinaryCode
  simpa only [executableScannedBetheOptimizerFloor] using
    executableScannedBetheOptimizer_finalFeasibilityResult
      hm A hApos hAupper

@[simp] theorem machineExplicitBetheOptimizerPointCode_encode
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1) :
    machineExplicitBetheOptimizerPointCode
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      rationalFiniteVectorCode (executableScannedBetheOptimizerPoint A) := by
  rw [machineExplicitBetheOptimizerPointCode,
    machineExplicitBetheOptimizerFeasibilityResultCode_encode
      hm A hApos hAupper]
  rfl

end BeyondBethe
