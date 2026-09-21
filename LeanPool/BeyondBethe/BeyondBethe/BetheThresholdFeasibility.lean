/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraphGeometry
import LeanPool.BeyondBethe.BeyondBethe.ScheduledFeasibility
import Mathlib.Tactic

/-! # Bethe Threshold Feasibility -/

namespace BeyondBethe

/-!
# Executable feasibility at a rational Bethe threshold

This file instantiates the generic rational ellipsoid loop with a completely
explicit zero-centered outer ball and the coordinate cross constructed from
an exact regularized optimizer.  The optimizer occurs only in the proof of
termination; the executable state, oracle, radius, and budget use rational
input data alone.
-/

/-- A square-root-free rational outer radius for the bounded epigraph cross. -/
def betheEpigraphOuterRadius (m : ℕ) (upper r : ℚ) : ℚ :=
  (m * m + 1) * (1 + abs upper + 2 * r)

theorem betheEpigraphOuterRadius_pos (m : ℕ) {upper r : ℚ}
    (hr : 0 ≤ r) : 0 < betheEpigraphOuterRadius m upper r := by
  rw [betheEpigraphOuterRadius]
  positivity

theorem cast_betheEpigraphOuterRadius (m : ℕ) (upper r : ℚ) :
    (betheEpigraphOuterRadius m upper r : ℝ) =
      ((m * m + 1 : ℕ) : ℝ) *
        (1 + abs (upper : ℝ) + 2 * (r : ℝ)) := by
  rw [betheEpigraphOuterRadius]
  push_cast
  rfl

/-- The exact call budget obtained from the explicit outer and inner radii. -/
def betheThresholdFeasibilityBudget (m : ℕ) (upper r : ℚ) : ℕ :=
  let d := m * m + 1
  32 * d ^ 3 * rationalBallDyadicExponent d
    (betheEpigraphOuterRadius m upper r) r

/-- Execute the complete rational oracle for one rational objective
threshold.  The initial ellipsoid is centered at zero and every parameter is
computed from the input rationals. -/
def runBetheThresholdFeasibility {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper r : ℚ) :
    RationalFeasibilityResult (m * m + 1) :=
  runScheduledRationalFeasibility (betheBoundedEpigraphOracle τ A p δ upper)
    (betheThresholdFeasibilityBudget m upper r)
    (rationalBallEllipsoid (m * m + 1) 0
      (betheEpigraphOuterRadius m upper r))

/-- Every accepted result of the specialized runner satisfies the exact
rational acceptance predicate of the complete oracle. -/
theorem runBetheThresholdFeasibility_acceptsOnly {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ upper r : ℚ) {q : Fin (m * m + 1) → ℚ}
    (hrun : runBetheThresholdFeasibility τ A p δ upper r = .accepted q) :
    BetheEpigraphOracleAccepted τ A p δ upper q := by
  exact runScheduledRationalFeasibility_acceptsOnly
    (betheBoundedEpigraphOracle_acceptsOnly τ A p δ upper)
    (by simpa only [runBetheThresholdFeasibility,
      betheThresholdFeasibilityBudget] using hrun)

/-- If a rational threshold has the displayed smoothing and height slack,
the executable feasibility run returns an accepted rational point. -/
theorem runBetheThresholdFeasibility_accepts_of_slack
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
      runBetheThresholdFeasibility τ A p δ upper r = .accepted q ∧
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
  obtain ⟨q, hrun, hgood⟩ := runScheduledRationalFeasibility_ball_accepts
    (d := m * m + 1) (by omega)
    (Target := BetheEpigraphTarget (τ : ℝ) (fun i j ↦ (A i j : ℝ))
      (δ : ℝ) (upper : ℝ))
    (Good := BetheEpigraphOracleAccepted τ A p δ upper)
    (oracle := betheBoundedEpigraphOracle τ A p δ upper)
    (betheBoundedEpigraphOracle_valid hm hτ0.le hτ1 hApos hδ p upper)
    (betheBoundedEpigraphOracle_acceptsOnly τ A p δ upper)
    (0 : Fin (m * m + 1) → ℚ) hR hr
    hcross'.1 hcross'.2
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
  simpa only [runBetheThresholdFeasibility,
    betheThresholdFeasibilityBudget] using hrun

/-- Conversely, exhaustion certifies that the queried threshold is strictly
below the exact optimum plus the smoothing slack.  This is a theorem about
the concrete runner, not an oracle assumption. -/
theorem runBetheThresholdFeasibility_exhausted_lt_optimum_add_slack
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
    (hrun : runBetheThresholdFeasibility τ A p δ upper r = .exhausted E) :
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
  obtain ⟨q, haccepted, _⟩ := runBetheThresholdFeasibility_accepts_of_slack
    hm hτ0 hτ1 hApos hAupper hX hmax hmix0 hmix1 hδ hr
      hspike hfloor hslack p
  rw [hrun] at haccepted
  contradiction

end BeyondBethe
