/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BetheThresholdFeasibility
import LeanPool.BeyondBethe.BeyondBethe.ExplicitScheduledFeasibility
import Mathlib.Tactic

/-! # Explicit Bethe Threshold Feasibility -/

namespace BeyondBethe

/-!
# Bethe threshold feasibility with the explicit ball schedule

This is the threshold runner implemented by the finite-word optimizer.  It
uses the same rational oracle and iteration budget as
`runBetheThresholdFeasibility`, but its rounding precision is computed from
the two explicit zero-ball exponents rather than a matrix LCM.
-/

def runExplicitBetheThresholdFeasibility {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper r : ℚ) :
    RationalFeasibilityResult (m * m + 1) :=
  let R := betheEpigraphOuterRadius m upper r
  runExplicitBallRationalFeasibility
    (betheBoundedEpigraphOracle τ A p δ upper)
    (betheThresholdFeasibilityBudget m upper r) R

theorem runExplicitBetheThresholdFeasibility_acceptsOnly {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper r : ℚ) {q : Fin (m * m + 1) → ℚ}
    (hrun : runExplicitBetheThresholdFeasibility τ A p δ upper r =
      .accepted q) :
    BetheEpigraphOracleAccepted τ A p δ upper q := by
  exact runExplicitBallRationalFeasibility_acceptsOnly
    (betheBoundedEpigraphOracle_acceptsOnly τ A p δ upper)
    (by simpa only [runExplicitBetheThresholdFeasibility,
      betheThresholdFeasibilityBudget] using hrun)

theorem runExplicitBetheThresholdFeasibility_accepts_of_slack
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix δ upper r : ℚ} (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hδ : 0 < δ) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : δ ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) τ)
    (hslack :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (upper : ℝ))
    (p : ℕ) :
    ∃ q : Fin (m * m + 1) → ℚ,
      runExplicitBetheThresholdFeasibility τ A p δ upper r =
          .accepted q ∧
        BetheEpigraphOracleAccepted τ A p δ upper q := by
  let δ0 : ℚ := numericalInteriorFloor (m + 1)
    (rationalMatrixEntryBitBound A) τ
  have hoptimizerFloor : ∀ i j, (δ0 : ℝ) ≤ X i j := by
    intro i j
    exact (regularizedOptimizer_meets_executable_floor
      (n := m + 1) (by omega) hτ0 hApos hAupper hX hmax i j).1
  have hcross := BetheEpigraphTarget_smoothed_inner_cross hm hτ0.le hτ1
    hApos hAupper hX hoptimizerFloor
    (Rat.cast_pos.mpr hmix0) (by exact_mod_cast hmix1)
    (Rat.cast_nonneg.mpr hr.le) (by
      have hs := (Rat.cast_le (K := ℝ)).mpr hspike
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hs
      simpa using hs)
    (δ := (δ : ℝ)) (upper := (upper : ℝ)) (by
      exact_mod_cast hfloor) hslack
  let ycenter := squareMatrixToVector (smoothedUniformAffineBase X (mix : ℝ))
  let zcenter := epigraphPoint ycenter ((upper : ℝ) - (r : ℝ))
  have hcross' :
      (∀ k, BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (δ : ℝ) (upper : ℝ)
          (fun i ↦ zcenter i + if i = k then (r : ℝ) else 0)) ∧
      (∀ k, BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (δ : ℝ) (upper : ℝ)
          (fun i ↦ zcenter i - if i = k then (r : ℝ) else 0)) := by
    simpa only [ycenter, zcenter] using hcross
  have houter := BetheEpigraphTarget_inner_cross_outer_zero hm
    (Rat.cast_nonneg.mpr hδ.le) (Rat.cast_nonneg.mpr hr.le) ycenter
    hcross'.1 hcross'.2
  have hR : 0 < betheEpigraphOuterRadius m upper r :=
    betheEpigraphOuterRadius_pos m hr.le
  obtain ⟨q, hrun, hgood⟩ :=
    runExplicitBallRationalFeasibility_ball_accepts
      (d := m * m + 1) (by omega)
      (Target := BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
        (δ : ℝ) (upper : ℝ))
      (Good := BetheEpigraphOracleAccepted τ A p δ upper)
      (oracle := betheBoundedEpigraphOracle τ A p δ upper)
      (betheBoundedEpigraphOracle_valid hm hτ0.le hτ1 hApos hδ p upper)
      (betheBoundedEpigraphOracle_acceptsOnly τ A p δ upper)
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
  simpa only [runExplicitBetheThresholdFeasibility,
    betheThresholdFeasibilityBudget] using hrun

theorem runExplicitBetheThresholdFeasibility_exhausted_lt_optimum_add_slack
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix δ upper r : ℚ} (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hδ : 0 < δ) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : δ ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) τ)
    (p : ℕ) {E : RationalEllipsoidState (m * m + 1)}
    (hrun : runExplicitBetheThresholdFeasibility τ A p δ upper r =
      .exhausted E) :
    (upper : ℝ) <
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) := by
  by_contra hnot
  have hslack :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (upper : ℝ) := not_lt.mp hnot
  obtain ⟨q, haccepted, _⟩ :=
    runExplicitBetheThresholdFeasibility_accepts_of_slack
      hm hτ0 hτ1 hApos hAupper hX hmax hmix0 hmix1 hδ hr
        hspike hfloor hslack p
  rw [hrun] at haccepted
  contradiction

end BeyondBethe
