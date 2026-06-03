/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
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
# PV Integral Splitting at Crossings

For a curve γ with a unique crossing of point s at parameter t₀, the PV cutoff
integral splits into left and right pieces — the near-crossing part vanishes.

The key observation: when ‖γ(t) - s‖ ≤ ε (i.e., t is near the crossing), the
cutoff integrand `if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0` is 0.
On the far segments, the cutoff condition is satisfied so the integrand equals
`(γ t - s)⁻¹ * deriv γ t` a.e.

## Main results

* `pv_split_at_crossing` — the PV cutoff integral equals the sum of left and
  right integrals of `(γ t - s)⁻¹ * deriv γ t`, where the middle part is zero.
-/

open Set MeasureTheory Complex Filter intervalIntegral

namespace ContourIntegral

/-- The PV cutoff integral splits at a crossing.

For ε, δ > 0 with δ < min(t₀ - a, b - t₀), if:
- the curve is far from s (norm > ε) outside the δ-window, and
- near to s (norm ≤ ε) inside the δ-window,

then the full cutoff integral equals the sum of the left and right integrals of
`(γ t - s)⁻¹ * deriv γ t`. The middle piece vanishes because the cutoff sets the
integrand to 0 whenever ‖γ t - s‖ ≤ ε. -/
theorem pv_split_at_crossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {ε δ : ℝ}
    {t₀ : ℝ} (_hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) (_hε : 0 < ε) (hδ : 0 < δ)
    (hδ_small : δ < min (t₀ - a) (b - t₀))
    (h_far : ∀ t ∈ Icc a b, δ < |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ t, |t - t₀| ≤ δ → ‖γ t - s‖ ≤ ε)
    (hint_left : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ))
    (hint_right : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ) b) :
    (∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
    (∫ t in a..(t₀ - δ), (γ t - s)⁻¹ * deriv γ t) +
    (∫ t in (t₀ + δ)..b, (γ t - s)⁻¹ * deriv γ t) := by
  -- Abbreviate the cutoff integrand
  set F := fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else (0 : ℂ) with hF_def
  -- Derive useful bounds from hδ_small
  have hδ_lt_left : δ < t₀ - a := lt_of_lt_of_le hδ_small (min_le_left _ _)
  have hδ_lt_right : δ < b - t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
  have ha_lt_t₀ : a < t₀ := ht₀.1
  have ht₀_lt_b : t₀ < b := ht₀.2
  have h_left_lt : a < t₀ - δ := by linarith
  have h_mid_lt : t₀ - δ < t₀ + δ := by linarith
  have h_right_lt : t₀ + δ < b := by linarith
  -- F = 0 on the middle segment [t₀ - δ, t₀ + δ]
  have hF_mid : ∀ t ∈ uIoc (t₀ - δ) (t₀ + δ), F t = 0 := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    simp only [hF_def]
    rw [if_neg (not_lt.mpr _)]
    apply h_near
    rw [abs_le]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  -- F = (γ t - s)⁻¹ * deriv γ t a.e. on [a, t₀ - δ]
  -- (The single boundary point t = t₀ - δ is measure zero; for all other t in Ioc a (t₀-δ)
  --  we have |t - t₀| > δ strictly, so h_far applies.)
  have hF_left : ∀ᵐ t ∂volume, t ∈ uIoc a (t₀ - δ) →
      F t = (γ t - s)⁻¹ * deriv γ t := by
    have h_ne : ({t₀ - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.finite_singleton _).measure_zero volume)
    filter_upwards [h_ne] with t ht_ne ht
    rw [uIoc_of_le (le_of_lt h_left_lt)] at ht
    simp only [hF_def]
    rw [if_pos]
    -- ht : t ∈ Ioc a (t₀ - δ), t ≠ t₀ - δ, so t < t₀ - δ, giving |t - t₀| > δ
    apply h_far t ⟨le_of_lt ht.1, le_trans ht.2 (by linarith)⟩
    rw [abs_of_nonpos (by linarith [ht.2])]
    have : t < t₀ - δ := lt_of_le_of_ne ht.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    linarith
  -- F = (γ t - s)⁻¹ * deriv γ t a.e. on [t₀ + δ, b]
  have hF_right : ∀ᵐ t ∂volume, t ∈ uIoc (t₀ + δ) b →
      F t = (γ t - s)⁻¹ * deriv γ t := by
    have h_ne : ({t₀ + δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.finite_singleton _).measure_zero volume)
    filter_upwards [h_ne] with t ht_ne ht
    rw [uIoc_of_le (le_of_lt h_right_lt)] at ht
    simp only [hF_def]
    rw [if_pos]
    -- ht : t ∈ Ioc (t₀ + δ) b, so t₀ + δ < t, giving |t - t₀| = t - t₀ > δ
    apply h_far t ⟨le_trans (by linarith) (le_of_lt ht.1), ht.2⟩
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.1]
  -- Integrability of F on each piece
  have hF_int_left : IntervalIntegrable F volume a (t₀ - δ) :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ) (t₀ + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ) (b := t₀ + δ)).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ) b :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  -- Split the full integral into three pieces
  have h_split : ∫ t in a..b, F t =
      (∫ t in a..(t₀ - δ), F t) + (∫ t in (t₀ - δ)..(t₀ + δ), F t) +
      (∫ t in (t₀ + δ)..b, F t) := by
    rw [← integral_add_adjacent_intervals (hF_int_left.trans hF_int_mid) hF_int_right,
        ← integral_add_adjacent_intervals hF_int_left hF_int_mid]
  -- Middle integral is zero
  have h_mid_zero : ∫ t in (t₀ - δ)..(t₀ + δ), F t = 0 := by
    rw [integral_congr_ae (ae_of_all _ (fun t ht => hF_mid t ht))]
    exact integral_zero
  -- Left integral: replace F by the full integrand
  have h_eq_left : ∫ t in a..(t₀ - δ), F t =
      ∫ t in a..(t₀ - δ), (γ t - s)⁻¹ * deriv γ t :=
    integral_congr_ae hF_left
  -- Right integral: replace F by the full integrand
  have h_eq_right : ∫ t in (t₀ + δ)..b, F t =
      ∫ t in (t₀ + δ)..b, (γ t - s)⁻¹ * deriv γ t :=
    integral_congr_ae hF_right
  -- Assemble
  rw [show (∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
      ∫ t in a..b, F t from rfl]
  rw [h_split, h_mid_zero, h_eq_left, h_eq_right]
  ring

end ContourIntegral
