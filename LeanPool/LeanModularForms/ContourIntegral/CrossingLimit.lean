/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ContourIntegral.PVSplit
import LeanPool.LeanModularForms.ContourIntegral.SegmentFTC
import Mathlib.Tactic.Common
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# Crossing Limit Theorem

The master theorem: for a closed piecewise C1 curve with a unique crossing
at t₀, the PV integral of (γ-s)⁻¹ · γ' equals the limit of the log ratio
log(g(t₀-δ)) - log(g(t₀+δ)) as δ → 0⁺.

This combines PVSplit (integral splitting) with SegmentFTC (telescoping)
to reduce PV computation to a single crossing-local limit.

## Main results

* `pv_tendsto_of_crossing_limit` — the PV integral tends to L if the log
  ratio at the crossing tends to L
-/

open Set MeasureTheory Complex Filter

namespace ContourIntegral

/-- Master crossing limit theorem: the PV integral of (γ-s)⁻¹ · γ' along a
curve with unique crossing at t₀ tends to L, provided:
1. For small ε, the curve is ε-far from s except near t₀
2. The far-segment integrals sum to some expression E(ε)
3. E(ε) → L as ε → 0⁺

The expression E(ε) is typically `log(g(t₀-δ)) - log(g(t₀+δ))` (simple case)
or `log(g(t₀-δ)) - log(g(t₀+δ)) + correction` (when the curve crosses a
branch cut of complex log, e.g., the `-2πi` correction at the elliptic point i).

This is the general version of the pattern used in all 6 ValenceFormula
winding number computations. -/
theorem pv_tendsto_of_crossing_limit
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {δ : ℝ → ℝ}
    {threshold : ℝ} (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min (t₀ - a) (b - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc a b, δ ε < |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ t - s‖ ≤ ε)
    -- The far-segment integrals equal some expression E(ε)
    {E : ℝ → ℂ}
    (h_ftc : ∀ ε, 0 < ε → ε < threshold →
      (∫ t in a..(t₀ - δ ε), (γ t - s)⁻¹ * deriv γ t) +
      (∫ t in (t₀ + δ ε)..b, (γ t - s)⁻¹ * deriv γ t) = E ε)
    (hint_left : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ ε))
    (hint_right : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ ε) b)
    -- E(ε) → L
    (h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε =>
      ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have hab : a < b := lt_trans ht₀.1 ht₀.2
  have h_ev : (fun ε => ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      =ᶠ[nhdsWithin 0 (Ioi 0)] E := by
    filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < threshold := hε.2
    rw [pv_split_at_crossing hab ht₀ hε_pos (hδ_pos ε hε_pos hε_lt)
        (hδ_small ε hε_pos hε_lt) (h_far ε hε_pos hε_lt) (h_near ε hε_pos hε_lt)
        (hint_left ε hε_pos hε_lt) (hint_right ε hε_pos hε_lt)]
    exact h_ftc ε hε_pos hε_lt
  exact h_limit.congr' h_ev.symm

/-- Asymmetric crossing limit: allows different cutoff radii on left and right
of the crossing point. Needed for corner crossings (e.g., ρ, ρ+1) where
the geometry differs on each side (e.g., vertical segment vs arc). -/
theorem pv_tendsto_of_crossing_limit_asymmetric
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {δ_left δ_right : ℝ → ℝ}
    {threshold : ℝ} (hthresh : 0 < threshold)
    (hδL_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε)
    (hδR_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε)
    (hδL_small : ∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀ - a)
    (hδR_small : ∀ ε, 0 < ε → ε < threshold → δ_right ε < b - t₀)
    (h_far_left : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Ico a (t₀ - δ_left ε), ε < ‖γ t - s‖)
    (h_far_right : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Ioc (t₀ + δ_right ε) b, ε < ‖γ t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (t₀ - δ_left ε) (t₀ + δ_right ε), ‖γ t - s‖ ≤ ε)
    {E : ℝ → ℂ}
    (h_ftc : ∀ ε, 0 < ε → ε < threshold →
      (∫ t in a..(t₀ - δ_left ε), (γ t - s)⁻¹ * deriv γ t) +
      (∫ t in (t₀ + δ_right ε)..b, (γ t - s)⁻¹ * deriv γ t) = E ε)
    (hint_left : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ_left ε))
    (hint_right : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ_right ε) b)
    (h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε =>
      ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have hab : a < b := lt_trans ht₀.1 ht₀.2
  have h_ev : (fun ε => ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      =ᶠ[nhdsWithin 0 (Ioi 0)] E := by
    filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < threshold := hε.2
    -- Derived bounds
    have hδL := hδL_pos ε hε_pos hε_lt
    have hδR := hδR_pos ε hε_pos hε_lt
    have hδL_bd := hδL_small ε hε_pos hε_lt
    have hδR_bd := hδR_small ε hε_pos hε_lt
    have h_left_lt : a < t₀ - δ_left ε := by linarith
    have h_right_lt : t₀ + δ_right ε < b := by linarith
    have h_mid_lt : t₀ - δ_left ε < t₀ + δ_right ε := by linarith
    -- Abbreviate the cutoff integrand
    set F := fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else (0 : ℂ) with hF_def
    -- F = 0 on the middle segment [t₀ - δL, t₀ + δR]
    have hF_mid : ∀ t ∈ uIoc (t₀ - δ_left ε) (t₀ + δ_right ε), F t = 0 := by
      intro t ht
      rw [uIoc_of_le (le_of_lt h_mid_lt)] at ht
      simp only [hF_def]
      rw [if_neg (not_lt.mpr _)]
      exact h_near ε hε_pos hε_lt t ⟨le_of_lt ht.1, ht.2⟩
    -- F = (γ t - s)⁻¹ * deriv γ t a.e. on [a, t₀ - δL]
    have hF_left : ∀ᵐ t ∂volume, t ∈ uIoc a (t₀ - δ_left ε) →
        F t = (γ t - s)⁻¹ * deriv γ t := by
      have h_ne : ({t₀ - δ_left ε} : Set ℝ)ᶜ ∈ ae volume :=
        mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.finite_singleton _).measure_zero volume)
      filter_upwards [h_ne] with t ht_ne ht_mem
      rw [uIoc_of_le (le_of_lt h_left_lt)] at ht_mem
      simp only [hF_def]
      rw [if_pos]
      apply h_far_left ε hε_pos hε_lt t
      exact ⟨le_of_lt ht_mem.1,
        lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))⟩
    -- F = (γ t - s)⁻¹ * deriv γ t a.e. on [t₀ + δR, b]
    have hF_right : ∀ᵐ t ∂volume, t ∈ uIoc (t₀ + δ_right ε) b →
        F t = (γ t - s)⁻¹ * deriv γ t := by
      have h_ne : ({t₀ + δ_right ε} : Set ℝ)ᶜ ∈ ae volume :=
        mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.finite_singleton _).measure_zero volume)
      filter_upwards [h_ne] with t ht_ne ht_mem
      rw [uIoc_of_le (le_of_lt h_right_lt)] at ht_mem
      simp only [hF_def]
      rw [if_pos]
      apply h_far_right ε hε_pos hε_lt t
      exact ⟨ht_mem.1, ht_mem.2⟩
    -- Integrability of F on each piece
    have hF_int_left : IntervalIntegrable F volume a (t₀ - δ_left ε) :=
      (hint_left ε hε_pos hε_lt).congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_left.mono (fun t ht hm => (ht hm).symm)))
    have hF_int_mid : IntervalIntegrable F volume (t₀ - δ_left ε) (t₀ + δ_right ε) :=
      (IntervalIntegrable.zero (μ := volume)
        (a := t₀ - δ_left ε) (b := t₀ + δ_right ε)).congr
        (fun t ht => (hF_mid t ht).symm)
    have hF_int_right : IntervalIntegrable F volume (t₀ + δ_right ε) b :=
      (hint_right ε hε_pos hε_lt).congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_right.mono (fun t ht hm => (ht hm).symm)))
    -- Split the full integral into three pieces
    have h_split : ∫ t in a..b, F t =
        (∫ t in a..(t₀ - δ_left ε), F t) +
        (∫ t in (t₀ - δ_left ε)..(t₀ + δ_right ε), F t) +
        (∫ t in (t₀ + δ_right ε)..b, F t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (hF_int_left.trans hF_int_mid) hF_int_right,
          ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
    -- Middle integral is zero
    have h_mid_zero : ∫ t in (t₀ - δ_left ε)..(t₀ + δ_right ε), F t = 0 :=
      intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht => hF_mid t ht))
    -- Left integral: replace F by the full integrand
    have h_eq_left : ∫ t in a..(t₀ - δ_left ε), F t =
        ∫ t in a..(t₀ - δ_left ε), (γ t - s)⁻¹ * deriv γ t :=
      intervalIntegral.integral_congr_ae hF_left
    -- Right integral: replace F by the full integrand
    have h_eq_right : ∫ t in (t₀ + δ_right ε)..b, F t =
        ∫ t in (t₀ + δ_right ε)..b, (γ t - s)⁻¹ * deriv γ t :=
      intervalIntegral.integral_congr_ae hF_right
    -- Assemble
    change ∫ t in a..b, F t = E ε
    rw [h_split, h_mid_zero, h_eq_left, h_eq_right]
    simp only [add_zero]
    exact h_ftc ε hε_pos hε_lt
  exact h_limit.congr' h_ev.symm

end ContourIntegral
