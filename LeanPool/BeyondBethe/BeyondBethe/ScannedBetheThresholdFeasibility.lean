/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheEpigraphOracle
import LeanPool.BeyondBethe.BeyondBethe.ExplicitScheduledFeasibility
import Mathlib.Tactic

/-! # Scanned Bethe Threshold Feasibility -/

namespace BeyondBethe

/-!
# Threshold feasibility for the implemented Bethe oracle

The finite-word oracle scans the floor constraints in row-major order.  This
file gives that exact oracle its semantic feasibility runner.  The older
`betheBoundedEpigraphOracle` may choose a different violated floor constraint;
no equality between the two tie-breaking rules is needed.
-/

def runExplicitScannedBetheThresholdFeasibility {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat) (r : ℚ) :
    RationalFeasibilityResult (m * m + 1) :=
  let R := betheEpigraphOuterRadius m upper.value r
  runExplicitBallRationalFeasibility
    (scannedBetheBoundedEpigraphOracle tau A p delta upper)
    (betheThresholdFeasibilityBudget m upper.value r) R

theorem runExplicitScannedBetheThresholdFeasibility_acceptsOnly {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat) (r : ℚ)
    {q : Fin (m * m + 1) → ℚ}
    (hrun : runExplicitScannedBetheThresholdFeasibility
      tau A p delta upper r = .accepted q) :
    BetheEpigraphOracleAccepted tau A p delta.value upper.value q := by
  exact runExplicitBallRationalFeasibility_acceptsOnly
    (scannedBetheBoundedEpigraphOracle_acceptsOnly tau A p delta upper)
    (by simpa only [runExplicitScannedBetheThresholdFeasibility,
      betheThresholdFeasibilityBudget] using hrun)

theorem runExplicitScannedBetheThresholdFeasibility_accepts_of_slack
    {m : ℕ} (hm : 0 < m) {tau : ℚ} (htau0 : 0 < tau)
    (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix r : ℚ} {delta upper : RawRat}
    (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hdelta : 0 < delta.value) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : delta.value ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) tau)
    (hslack :
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (upper.value : ℝ))
    (p : ℕ) :
    ∃ q : Fin (m * m + 1) → ℚ,
      runExplicitScannedBetheThresholdFeasibility
          tau A p delta upper r = .accepted q ∧
        BetheEpigraphOracleAccepted
          tau A p delta.value upper.value q := by
  let delta0 : ℚ := numericalInteriorFloor (m + 1)
    (rationalMatrixEntryBitBound A) tau
  have hoptimizerFloor : ∀ i j, (delta0 : ℝ) ≤ X i j := by
    intro i j
    exact (regularizedOptimizer_meets_executable_floor
      (n := m + 1) (by omega) htau0 hApos hAupper hX hmax i j).1
  have hcross := BetheEpigraphTarget_smoothed_inner_cross hm htau0.le htau1
    hApos hAupper hX hoptimizerFloor
    (Rat.cast_pos.mpr hmix0) (by exact_mod_cast hmix1)
    (Rat.cast_nonneg.mpr hr.le) (by
      have hs := (Rat.cast_le (K := ℝ)).mpr hspike
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hs
      simpa using hs)
    (δ := (delta.value : ℝ)) (upper := (upper.value : ℝ)) (by
      exact_mod_cast hfloor) hslack
  let ycenter := squareMatrixToVector (smoothedUniformAffineBase X (mix : ℝ))
  let zcenter := epigraphPoint ycenter ((upper.value : ℝ) - (r : ℝ))
  have hcross' :
      (∀ k, BetheEpigraphTarget (tau : ℝ) (fun i j ↦ (A i j : ℝ))
        (delta.value : ℝ) (upper.value : ℝ)
          (fun i ↦ zcenter i + if i = k then (r : ℝ) else 0)) ∧
      (∀ k, BetheEpigraphTarget (tau : ℝ) (fun i j ↦ (A i j : ℝ))
        (delta.value : ℝ) (upper.value : ℝ)
          (fun i ↦ zcenter i - if i = k then (r : ℝ) else 0)) := by
    simpa only [ycenter, zcenter] using hcross
  have houter := BetheEpigraphTarget_inner_cross_outer_zero hm
    (Rat.cast_nonneg.mpr hdelta.le) (Rat.cast_nonneg.mpr hr.le) ycenter
    hcross'.1 hcross'.2
  have hR : 0 < betheEpigraphOuterRadius m upper.value r :=
    betheEpigraphOuterRadius_pos m hr.le
  obtain ⟨q, hrun, hgood⟩ :=
    runExplicitBallRationalFeasibility_ball_accepts
      (d := m * m + 1) (by omega)
      (Target := BetheEpigraphTarget (tau : ℝ) (fun i j ↦ (A i j : ℝ))
        (delta.value : ℝ) (upper.value : ℝ))
      (Good := BetheEpigraphOracleAccepted
        tau A p delta.value upper.value)
      (oracle := scannedBetheBoundedEpigraphOracle tau A p delta upper)
      (scannedBetheBoundedEpigraphOracle_valid hm htau0.le htau1
        hApos hdelta p upper)
      (scannedBetheBoundedEpigraphOracle_acceptsOnly tau A p delta upper)
      hR hr hcross'.1 hcross'.2
      (by
        intro k
        have hk := houter.1 k
        rw [cast_betheEpigraphOuterRadius]
        simpa [zcenter, ycenter] using hk)
      (by
        intro k
        have hk := houter.2 k
        rw [cast_betheEpigraphOuterRadius]
        simpa [zcenter, ycenter] using hk)
  refine ⟨q, ?_, hgood⟩
  simpa only [runExplicitScannedBetheThresholdFeasibility,
    betheThresholdFeasibilityBudget] using hrun

theorem runExplicitScannedBetheThresholdFeasibility_exhausted_lt_optimum_add_slack
    {m : ℕ} (hm : 0 < m) {tau : ℚ} (htau0 : 0 < tau)
    (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix r : ℚ} {delta upper : RawRat}
    (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hdelta : 0 < delta.value) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : delta.value ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) tau)
    (p : ℕ) {E : RationalEllipsoidState (m * m + 1)}
    (hrun : runExplicitScannedBetheThresholdFeasibility
      tau A p delta upper r = .exhausted E) :
    (upper.value : ℝ) <
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) := by
  by_contra hnot
  have hslack :
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (upper.value : ℝ) := not_lt.mp hnot
  obtain ⟨q, haccepted, _⟩ :=
    runExplicitScannedBetheThresholdFeasibility_accepts_of_slack
      hm htau0 htau1 hApos hAupper hX hmax hmix0 hmix1 hdelta hr
        hspike hfloor hslack p
  rw [hrun] at haccepted
  contradiction

end BeyondBethe
