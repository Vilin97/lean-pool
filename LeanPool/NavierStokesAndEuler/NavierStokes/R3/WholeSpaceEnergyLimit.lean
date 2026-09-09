/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFiniteEnergy
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonGronwall
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedDifferenceEnergy
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Removing the spatial energy cutoff

At a fixed time, square integrability gives an integrable dominating function.
This module removes the cutoff only after that hypothesis has been supplied.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.WholeSpaceEnergyLimit

open ProblemStatement Comparison ComparisonCutoffs

theorem integral_weight_tendsto {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) :
    Tendsto (fun R : ℝ => ∫ x : Space, weight R x * ‖w x‖ ^ 2)
      atTop (𝓝 (l2Sq w)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : Space => ‖w x‖ ^ 2)
  · exact Filter.Eventually.of_forall fun R =>
      ((weight_smooth R).continuous.mul (hw.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg R x) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_le_one R x)
  · exact hi
  · exact Filter.Eventually.of_forall fun x => by
      have h := ((cutoff_tendsto_one x).pow 8).mul_const (‖w x‖ ^ 2)
      simpa only [weight, one_pow, one_mul] using h

theorem eq_zero_of_l2Sq_eq_zero {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) (hz : l2Sq w = 0) :
    ∀ x : Space, w x = 0 := by
  have hae : (fun x : Space => ‖w x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hz
  have heq : (fun x : Space => ‖w x‖ ^ 2) = (fun _ : Space => (0 : ℝ)) :=
    Measure.eq_of_ae_eq hae (hw.norm.pow 2) continuous_const
  intro x
  have hx : ‖w x‖ ^ 2 = 0 := congrFun heq x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A bound on actual weighted integrals, uniform over large radii, forces a
continuous square-integrable field to vanish everywhere. -/
theorem eq_zero_of_radius_bound {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) {D R₀ : ℝ}
    (hbound : ∀ R : ℝ, max 1 R₀ ≤ R →
      (∫ x : Space, weight R x * ‖w x‖ ^ 2) ≤ D / R) :
    ∀ x : Space, w x = 0 := by
  have hlim := integral_weight_tendsto hw hi
  have hz : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atTop (𝓝 D)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have hle : l2Sq w ≤ 0 :=
    le_of_tendsto_of_tendsto hlim hz (eventually_atTop.2 ⟨max 1 R₀, hbound⟩)
  exact eq_zero_of_l2Sq_eq_zero hw hi
    (le_antisymm hle (integral_nonneg fun x => sq_nonneg _))

/-- The final scalar and cutoff step of uniqueness. The differential estimate
is an explicit input here; deriving it from the PDE and pressure is separate. -/
theorem eq_zero_of_weighted_rate_bound {w : VelocityField} {T K C R₀ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, SquareIntegrableAtTime w t)
    (hzero : ∀ x : Space, w (0, x) = 0)
    (hrate : ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) w t ≤ K * weightedEnergy (weight R) w t + C / R) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, w (t, x) = 0 := by
  intro t ht
  have hs := NavierStokes.PeriodicUniqueness.spatial_smooth hw ht
  apply eq_zero_of_radius_bound hs.continuous (hi t ht)
    (D := C * T * Real.exp (K * T)) (R₀ := R₀)
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hcont := LocalizedDifferenceEnergy.weightedEnergy_continuousOn
    (weight_smooth R).continuous (weight_hasCompactSupport hRpos) hw
  have hinit : weightedEnergy (weight R) w 0 = 0 := by
    simp [weightedEnergy, hzero]
  exact ComparisonGronwall.le_div_radius_of_deriv_le hT hK hC hRpos hcont hinit
    (fun s hs => LocalizedDifferenceEnergy.weightedEnergy_hasDerivAt
      (weight_smooth R) (weight_hasCompactSupport hRpos) hw hs)
    (hrate R hR) t ht

end NavierStokesR3.WholeSpaceEnergyLimit
