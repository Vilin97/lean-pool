/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Arbitrarily tight rounded support envelopes

The quantitative support-envelope estimate becomes an arbitrary open
neighborhood estimate after choosing the smoothing and rounding scales.  We
record an explicit choice that remains valid even for one-point finite sets,
where the logarithmic cardinality term vanishes.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportEnvelopeApproximation
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportCurve

open Complex Metric Set
open scoped ContDiff

/-- Every nonempty finite convex hull has positive log-sum-exp smoothing
and rounding scales whose open envelope contains the hull while the closure
of that envelope stays in a prescribed metric thickening. -/
theorem exists_tight_polytopeRoundedSupportEnvelope
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) := by
  let L : ℝ := Real.log (u.card : ℝ)
  let Q : ℝ := max 1 L
  let delta : ℝ := epsilon / (4 * Q)
  let rho : ℝ := epsilon / 4
  have hcard : (1 : ℝ) ≤ (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg hcard
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 L)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos hepsilon (mul_pos (by norm_num) hQ)
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have hLQ : L ≤ Q := by
    dsimp only [Q]
    exact le_max_right 1 L
  have hdeltaQ : delta * Q = epsilon / 4 := by
    dsimp only [delta]
    field_simp [hQ.ne']
  have hdeltaL : delta * L ≤ epsilon / 4 := by
    calc
      delta * L ≤ delta * Q :=
        mul_le_mul_of_nonneg_left hLQ hdelta.le
      _ = epsilon / 4 := hdeltaQ
  have hovershoot : delta * Real.log (u.card : ℝ) + rho < epsilon := by
    change delta * L + rho < epsilon
    dsimp only [rho]
    linarith
  refine ⟨delta, rho, hdelta, hrho,
    convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hdelta hrho, ?_⟩
  exact
    (closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho).trans
      (Metric.cthickening_subset_thickening'
        hepsilon hovershoot (convexHull ℝ (u : Set ℂ)))

/-- The tight-envelope parameters simultaneously give a smooth, periodic,
everywhere regular support curve. -/
theorem exists_tight_regular_polytopeRoundedSupportCurve
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) ∧
      Function.Periodic (polytopeRoundedSupportCurve u delta rho)
        (2 * Real.pi) ∧
      ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) ∧
      ∀ theta, deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by
  obtain ⟨delta, rho, hdelta, hrho, hin, hout⟩ :=
    exists_tight_polytopeRoundedSupportEnvelope hu hepsilon
  exact ⟨delta, rho, hdelta, hrho, hin, hout,
    periodic_polytopeRoundedSupportCurve u delta rho,
    contDiff_polytopeRoundedSupportCurve hu delta rho,
    polytopeRoundedSupportCurve_regular hu hdelta hrho⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
