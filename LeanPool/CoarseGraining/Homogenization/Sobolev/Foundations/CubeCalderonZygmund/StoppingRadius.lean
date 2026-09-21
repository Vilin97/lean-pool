/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambda
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Stopping Radius -/

namespace Homogenization

open scoped ENNReal NNReal BigOperators Topology
open Filter MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Continuous stopping radii

This file supplies the continuous-radius ingredient for the Vitali route in
the cube Calderón--Zygmund argument.  The ambient `Vec d` carries its sup
metric, so its metric closed balls are axis-parallel cubes.
-/

/-- A continuous function that starts above a level and ends below it has a
last radius at the level; after that radius it stays below the level. -/
theorem exists_last_crossing_of_continuousOn {E : ℝ → ℝ} {a b level : ℝ}
    (hab : a ≤ b) (hE : ContinuousOn E (Icc a b))
    (ha : level < E a) (hb : E b ≤ level) :
    ∃ r ∈ Icc a b, E r = level ∧ ∀ s ∈ Icc r b, E s ≤ level := by
  let S : Set ℝ := Icc a b ∩ E ⁻¹' Ici level
  have hS_closed : IsClosed S := by
    exact hE.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed inter_subset_left
  have haS : a ∈ S := by
    exact ⟨⟨le_rfl, hab⟩, le_of_lt ha⟩
  obtain ⟨r, hrS, hrmax⟩ := hS_compact.exists_isGreatest ⟨a, haS⟩
  have hr_eq : E r = level := by
    have hr_ge : level ≤ E r := hrS.2
    by_contra hne
    have hr_gt : level < E r := lt_of_le_of_ne hr_ge (Ne.symm hne)
    obtain ⟨s, hsIcc, hsE⟩ :=
      intermediate_value_Icc' hrS.1.2 (hE.mono (Icc_subset_Icc_left hrS.1.1))
        ⟨hb, hr_gt.le⟩
    have hrs : r ≤ s := hsIcc.1
    have hrs_ne : r ≠ s := by
      intro hrs_eq
      subst s
      exact (ne_of_gt hr_gt) hsE
    exact
      (not_lt_of_ge (hrmax ⟨⟨hrS.1.1.trans hsIcc.1, hsIcc.2⟩, hsE.ge⟩))
        (lt_of_le_of_ne hrs hrs_ne)
  refine ⟨r, hrS.1, hr_eq, ?_⟩
  intro s hs
  by_contra hs_not
  have hs_gt : level < E s := lt_of_not_ge hs_not
  have hrs_ne : r ≠ s := by
    intro hrs_eq
    subst s
    exact (ne_of_gt hs_gt) hr_eq
  exact
    (not_lt_of_ge (hrmax ⟨⟨hrS.1.1.trans hs.1, hs.2⟩, hs_gt.le⟩))
      (lt_of_le_of_ne hs.1 hrs_ne)

/-- In positive dimension, a sup-metric sphere in `Vec d` has zero Lebesgue
measure.  This is the boundary-null fact used by dominated convergence below. -/
theorem volume_sphere_eq_zero {d : ℕ} [NeZero d] (x : Vec d) (r : ℝ) :
    volume (Metric.sphere x r) = 0 := by
  rw [← MeasureTheory.addHaarMeasure_eq_volume_pi (Fin d)]
  exact MeasureTheory.Measure.addHaar_sphere _ x r

/-- The integral of an integrable function over a sup-metric closed ball is
continuous as a function of its positive radius. -/
theorem continuousOn_setIntegral_closedBall {d : ℕ} [NeZero d]
    (f : Vec d → ℝ) (hf : Integrable f volume) (x : Vec d) :
    ContinuousOn (fun r => ∫ y in Metric.closedBall x r, f y ∂volume) (Ioi 0) := by
  intro r hr
  change Tendsto (fun s => ∫ y in Metric.closedBall x s, f y ∂volume)
    (𝓝[Ioi 0] r) (𝓝 (∫ y in Metric.closedBall x r, f y ∂volume))
  have hsphere_ae : ∀ᵐ y ∂volume, y ∉ Metric.sphere x r := by
    rw [ae_iff]
    simpa using! (volume_sphere_eq_zero (d := d) x r)
  have hlim : ∀ᵐ y ∂volume,
      Tendsto (fun s => (Metric.closedBall x s).indicator f y) (𝓝[Ioi 0] r)
        (𝓝 ((Metric.closedBall x r).indicator f y)) := by
    filter_upwards [hsphere_ae] with y hy
    by_cases hyr : dist y x < r
    · apply Filter.EventuallyEq.tendsto
      filter_upwards [(eventually_gt_nhds hyr).filter_mono nhdsWithin_le_nhds] with s hys
      rw [Set.indicator_of_mem (Metric.mem_closedBall.mpr hys.le),
        Set.indicator_of_mem (Metric.mem_closedBall.mpr hyr.le)]
    · have hry_le : r ≤ dist y x := le_of_not_gt hyr
      have hry_ne : dist y x ≠ r := by
        intro hry
        exact hy (Metric.mem_sphere.mpr hry)
      have hry : r < dist y x := lt_of_le_of_ne hry_le (Ne.symm hry_ne)
      apply Filter.EventuallyEq.tendsto
      filter_upwards [(eventually_lt_nhds hry).filter_mono nhdsWithin_le_nhds] with s hs
      rw [Set.indicator_of_notMem (by simpa only [Metric.mem_closedBall, not_le] using hs),
        Set.indicator_of_notMem (by simpa only [Metric.mem_closedBall, not_le] using hry)]
  have hdom : ∀ᶠ s in 𝓝[Ioi 0] r, ∀ᵐ y ∂volume,
      ‖(Metric.closedBall x s).indicator f y‖ ≤ ‖f y‖ := by
    filter_upwards [] with s
    filter_upwards [] with y
    by_cases hy : y ∈ Metric.closedBall x s
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      simp only [norm_zero]
      exact norm_nonneg _
  have hmeas : ∀ᶠ s in 𝓝[Ioi 0] r,
      AEStronglyMeasurable ((Metric.closedBall x s).indicator f) volume := by
    filter_upwards [] with s
    exact hf.aestronglyMeasurable.indicator measurableSet_closedBall
  simpa only [integral_indicator measurableSet_closedBall] using
    (tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) hmeas hdom hf.norm hlim)

/-- The normalized integral over the sup-metric ball.  At positive radii this
is the usual set average, since the ball has volume `(2r)^d`. -/
def closedBallAverage {d : ℕ} (x : Vec d) (r : ℝ) (f : Vec d → ℝ) : ℝ :=
  ((2 * r) ^ d)⁻¹ * ∫ y in Metric.closedBall x r, f y ∂volume

theorem closedBallAverage_eq_setAverage {d : ℕ} (x : Vec d) {r : ℝ}
    (hr : 0 ≤ r) (f : Vec d → ℝ) :
    closedBallAverage x r f = ⨍ y in Metric.closedBall x r, f y ∂volume := by
  have h2r : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr
  have hpow : 0 ≤ (2 * r) ^ Fintype.card (Fin d) := pow_nonneg h2r _
  rw [closedBallAverage, MeasureTheory.setAverage_eq, smul_eq_mul,
    MeasureTheory.measureReal_def, Real.volume_pi_closedBall x hr,
    ENNReal.toReal_ofReal hpow]
  simp only [Fintype.card_fin]

/-- Positive-radius normalized closed-ball averages of integrable data are
continuous in the radius. -/
theorem continuousOn_closedBallAverage {d : ℕ} [NeZero d]
    (f : Vec d → ℝ) (hf : Integrable f volume) (x : Vec d) :
    ContinuousOn (fun r => closedBallAverage x r f) (Ioi 0) := by
  have hdenom : ContinuousOn (fun r : ℝ => ((2 * r) ^ d)⁻¹) (Ioi 0) := by
    apply ((continuous_const.mul continuous_id).continuousOn.pow d).inv₀
    intro r hr
    exact pow_ne_zero d (mul_ne_zero (by norm_num) (ne_of_gt hr))
  simpa only [closedBallAverage] using!
    hdenom.mul (continuousOn_setIntegral_closedBall f hf x)

/-- The normalized local squared energy over a sup-metric closed ball. -/
def closedBallL2Energy {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (u : Vec d → F) (x : Vec d) (r : ℝ) : ℝ :=
  closedBallAverage x r fun y => ‖u y‖ ^ 2

/-- Integrable square data has a continuous normalized local `L²` energy on
positive radii. -/
theorem continuousOn_closedBallL2Energy {d : ℕ} [NeZero d]
    {F : Type*} [NormedAddCommGroup F] (u : Vec d → F)
    (hu : Integrable (fun y => ‖u y‖ ^ 2) volume) (x : Vec d) :
    ContinuousOn (fun r => closedBallL2Energy u x r) (Ioi 0) :=
  continuousOn_closedBallAverage (fun y => ‖u y‖ ^ 2) hu x

end CubeCalderonZygmund

end

end Homogenization
