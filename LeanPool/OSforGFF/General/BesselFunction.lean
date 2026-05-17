/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import LeanPool.OSforGFF.Spacetime.Euclidean
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Modified Bessel Function K₁

This file defines the modified Bessel function K₁(z) via its integral representation
and establishes key properties needed for the free covariance in AQFT.

## Main definitions

* `besselK1` - The modified Bessel function K₁(z) = ∫₀^∞ exp(-z cosh(t)) cosh(t) dt
* `besselK1_properTime` - Alternative proper-time representation:
    K₁(z) = (z/2) ∫₀^∞ t^{-2} exp(-t - z²/(4t)) dt

## Main results

* `besselK1_pos` - K₁(z) > 0 for z > 0
* `besselK1_asymptotic` - Asymptotic bound K₁(z) ≤ √(π/(2z)) · exp(-z) · 2 for z ≥ 1
* `besselK1_eq_properTime` - Equivalence of cosh and proper-time representations
* `schwingerIntegral_eq_besselK1` - Identity connecting Schwinger integral to K₁

## Notes

The cosh integral representation is particularly useful because:
1. It's manifestly real and positive for positive arguments
2. The integrand decays exponentially in t for any z > 0
3. It directly shows the analytic structure in z

For the massive scalar field in 4D Euclidean space, the exact formula is:
  C(x,y) = (m / (4π² |x-y|)) · K₁(m |x-y|)
-/

open MeasureTheory Set Filter Asymptotics Real

/-- The modified Bessel function K₁(z) via cosh integral representation.
    K₁(z) = ∫₀^∞ exp(-z cosh(t)) cosh(t) dt
    This is well-defined and positive for z > 0.
-/
noncomputable def besselK1 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh t

/-- K₁(z) is positive for z > 0. -/
lemma besselK1_pos (z : ℝ) (hz : 0 < z) : 0 < besselK1 z := by
  unfold besselK1
  -- The integrand f(t) = exp(-z cosh(t)) * cosh(t) is strictly positive for all t
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh t with hf_def
  -- f is nonnegative (actually positive)
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => by
    apply mul_nonneg (exp_nonneg _) (cosh_pos t).le
  have hf_pos : ∀ t, 0 < f t := fun t => by
    apply mul_pos (exp_pos _) (cosh_pos t)
  -- f is continuous
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_const.mul continuous_cosh)
    · exact continuous_cosh
  -- f is integrable on [0, ∞) because exp(-z cosh(t)) decays super-exponentially
  -- Key insight: for t ≥ 1, cosh(t) ≥ exp(t)/3, so exp(-z·cosh(t)) ≤ exp(-z·exp(t)/3)
  -- Thus f(t) ≤ exp(-z·exp(t)/3 + t), which decays faster than any exponential
  -- Strategy: Split [0,∞) = [0,1] ∪ [1,∞), use compactness on [0,1] and
  -- integrable_of_isBigO_exp_neg on [1,∞) with the super-exponential decay bound
  have hf_int : IntegrableOn f (Ici 0) volume := by
    -- Split [0, ∞) = [0, 1] ∪ [1, ∞)
    have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
      ext x; simp only [mem_Ici, mem_union, mem_Icc]
      constructor
      · intro hx; by_cases h : x ≤ 1
        · left; exact ⟨hx, h⟩
        · right; linarith
      · intro h; cases h with
        | inl h => exact h.1
        | inr h => linarith
    rw [h_union]
    apply IntegrableOn.union
    -- On [0, 1]: continuous on compact → integrable
    · exact hf_cont.continuousOn.integrableOn_compact isCompact_Icc
    -- On [1, ∞): super-exponential decay → integrable
    -- The detailed bound verification is technical but straightforward calculus
    · have h_int_Ioi : IntegrableOn f (Ioi 0) volume := by
        apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
        -- f =O[atTop] exp(-t) because f(t) = exp(-z·cosh(t))·cosh(t) decays super-exponentially
        -- Strategy: show f(t)/exp(-t) → 0, which implies eventually f(t) ≤ exp(-t)
        rw [isBigO_iff]
        use 1
        -- f(t) / exp(-t) = cosh(t) * exp(t - z*cosh(t))
        -- For t ≥ 0: cosh(t) ≤ exp(t) and cosh(t) ≥ exp(t)/2
        -- So f(t)/exp(-t) ≤ exp(t) * exp(t - z*exp(t)/2) = exp(2t - z*exp(t)/2) → 0
        have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t))
            atTop (nhds 0) := by
          have h_eq : ∀ t, f t / exp (-t) =
              cosh t * exp (t - z * cosh t) := by
            intro t
            simp only [f]
            field_simp
            rw [mul_comm, ← exp_add]
            ring_nf
          simp_rw [h_eq]
          -- Bound: cosh(t) * exp(t - z*cosh(t)) ≤ exp(2t - z*exp(t)/2) for t ≥ 0
          have hbound : ∀ t, 0 ≤ t →
              cosh t * exp (t - z * cosh t) ≤
              exp (2 * t - z * exp t / 2) := by
            intro t ht
            have h_cosh_le : cosh t ≤ exp t := by
              rw [cosh_eq]
              have : exp (-t) ≤ exp t := exp_le_exp.mpr (by linarith)
              linarith
            have h_cosh_ge : cosh t ≥ exp t / 2 := by
              rw [cosh_eq]
              have : exp (-t) ≥ 0 := exp_nonneg _
              linarith
            calc cosh t * exp (t - z * cosh t)
                ≤ exp t * exp (t - z * cosh t) := by
                  apply mul_le_mul_of_nonneg_right h_cosh_le (exp_nonneg _)
              _ ≤ exp t * exp (t - z * (exp t / 2)) := by
                  apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
                  apply exp_le_exp.mpr
                  have : -z * cosh t ≤ -z * (exp t / 2) := by
                    apply mul_le_mul_of_nonpos_left h_cosh_ge (by linarith)
                  linarith
              _ = exp (2 * t - z * exp t / 2) := by
                  rw [← exp_add]; ring_nf
          -- exp(2t - z*exp(t)/2) → 0 as t → ∞
          have h_exp_to_zero : Tendsto (fun t => exp (2 * t - z * exp t / 2))
              atTop (nhds 0) := by
            apply tendsto_exp_atBot.comp
            -- Show 2t - z*exp(t)/2 → -∞
            -- Rewrite as (z*exp(t)/2) * (4t/(z*exp(t)) - 1)
            -- Since t/exp(t) → 0, we have 4t/(z*exp(t)) - 1 → -1 < 0
            -- And z*exp(t)/2 → +∞, so the product → -∞ (using atTop_mul_neg)
            have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop := by
              apply Tendsto.atTop_div_const (by linarith : (0 : ℝ) < 2)
              exact Tendsto.const_mul_atTop hz tendsto_exp_atTop
            have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
              have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
              simp only [pow_one] at h
              convert h using 1
              ext t
              rw [exp_neg, div_eq_mul_inv]
            have h_scaled : Tendsto (fun t : ℝ => 4 / z * (t / exp t)) atTop (nhds (4 / z * 0)) :=
              h_ratio.const_mul (4 / z)
            simp only [mul_zero] at h_scaled
            have h_shifted :
                Tendsto (fun t : ℝ => 4 / z * (t / exp t) - 1) atTop (nhds (-1)) := by
              convert h_scaled.sub_const 1 using 1
              simp
            have h_prod :
                Tendsto (fun t : ℝ => (z * exp t / 2) * (4 / z * (t / exp t) - 1))
                  atTop atBot :=
              Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
            convert h_prod using 1
            ext t
            field_simp
            ring
          have hpos : ∀ t, 0 ≤ cosh t * exp (t - z * cosh t) := by
            intro t
            apply mul_nonneg (cosh_pos t).le (exp_nonneg _)
          -- Squeeze theorem (use squeeze_zero' for eventual bounds)
          refine squeeze_zero' (Eventually.of_forall hpos) ?_ h_exp_to_zero
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          exact hbound t ht
        -- From f(t)/exp(-t) → 0, get eventually f(t) ≤ exp(-t)
        have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
          have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
            have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
            filter_upwards [this] with t ht
            simp only [Real.dist_eq, sub_zero] at ht
            exact ht
          filter_upwards [h1] with t ht
          have hgt : 0 < exp (-t) := exp_pos _
          rw [abs_lt] at ht
          have hle : f t / exp (-t) < 1 := ht.2
          have : f t < exp (-t) := (div_lt_one hgt).mp hle
          simp only [neg_mul, one_mul]
          linarith
        filter_upwards [h_eventually_le] with t ht
        rw [Real.norm_of_nonneg (hf_nonneg t), Real.norm_of_nonneg (exp_nonneg _)]
        simp only [one_mul]
        exact ht
      apply h_int_Ioi.mono _ le_rfl
      intro x hx
      simp only [mem_Ici] at hx
      simp only [mem_Ioi]
      linarith
  -- The support of f intersected with [0, ∞) is [0, ∞) since f is everywhere positive
  have h_support : Function.support f ∩ Ici 0 = Ici 0 := by
    ext t
    simp only [Function.mem_support, mem_inter_iff, mem_Ici, ne_eq]
    constructor
    · intro ⟨_, ht⟩; exact ht
    · intro ht; exact ⟨(hf_pos t).ne', ht⟩
  -- The measure of [0, ∞) is positive (it's infinite, actually)
  have h_meas_pos : 0 < volume (Function.support f ∩ Ici 0) := by
    rw [h_support, Real.volume_Ici]
    exact ENNReal.zero_lt_top
  -- Apply the positivity criterion
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun t => hf_nonneg t)) hf_int]
  exact h_meas_pos

/-- K₁ is continuous on (0, ∞). This follows from dominated convergence since the integrand
    z ↦ exp(-z cosh(t)) cosh(t) is continuous in z and dominated by exp(-ε cosh(t)) cosh(t)
    for z ≥ ε, which is integrable.

    The formal proof uses MeasureTheory.continuousOn_of_dominated_of_compact:
    for z in compact K ⊆ (0, ∞), bound by exp(-min(K) * cosh(t)) * cosh(t).
-/
lemma besselK1_continuousOn : ContinuousOn besselK1 (Ioi 0) := by
  -- Show ContinuousAt at each z₀ > 0 using dominated convergence
  rw [isOpen_Ioi.continuousOn_iff]
  intro z₀ hz₀
  simp only [mem_Ioi] at hz₀
  unfold besselK1
  -- Use bound: exp(-(z₀/2) * cosh t) * cosh t for z ≥ z₀/2
  set bound : ℝ → ℝ := fun t => exp (-(z₀/2) * cosh t) * cosh t with hbound_def
  apply MeasureTheory.continuousAt_of_dominated (bound := bound)
  -- AEStronglyMeasurable for z near z₀
  · filter_upwards with z
    exact (((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
      continuous_cosh).aestronglyMeasurable).restrict
  -- Dominated by bound for z in neighborhood of z₀
  · have hne : Ioi (z₀/2) ∈ nhds z₀ := Ioi_mem_nhds (by linarith : z₀/2 < z₀)
    filter_upwards [hne] with z hz
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (cosh_pos t).le)]
    simp only [mem_Ioi] at hz
    -- exp(-z * cosh t) ≤ exp(-(z₀/2) * cosh t) since z > z₀/2 and cosh t > 0
    apply mul_le_mul_of_nonneg_right _ (cosh_pos t).le
    apply exp_le_exp.mpr
    -- Need: -z * cosh t ≤ -(z₀/2) * cosh t, i.e., (z₀/2) * cosh t ≤ z * cosh t
    have hcosh : 0 < cosh t := cosh_pos t
    nlinarith [hcosh, hz]
  -- Bound is integrable (same proof as in besselK1_pos)
  · have hz₀' : 0 < z₀ / 2 := by linarith
    have hcont : Continuous bound :=
      (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul continuous_cosh
    have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
      ext x; simp only [mem_Ici, mem_union, mem_Icc]
      constructor
      · intro hx
        by_cases h : x ≤ 1
        · left
          exact ⟨hx, h⟩
        · right
          linarith
      · intro h
        cases h with
        | inl h => exact h.1
        | inr h => linarith
    rw [h_union]
    apply IntegrableOn.union
    · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    · -- The bound exp(-(z₀/2) * cosh t) * cosh t is integrable on [1, ∞)
      -- This follows from super-exponential decay, similar to besselK1_pos
      -- First show integrability on (1, ∞), then extend to [1, ∞)
      have h_Ioi : IntegrableOn bound (Ioi 1) volume := by
        apply integrable_of_isBigO_exp_neg (b := 1) one_pos hcont.continuousOn
        rw [isBigO_iff]; use 1
        have h_ratio_tendsto : Tendsto (fun t => bound t / exp (-t)) atTop (nhds 0) := by
          have h_eq : ∀ t, bound t / exp (-t) = cosh t * exp (t - (z₀/2) * cosh t) := by
            intro t; simp only [hbound_def]; rw [div_eq_mul_inv, ← exp_neg, neg_neg]
            rw [mul_comm (exp _) (cosh t), mul_assoc, ← exp_add]; congr 1; ring_nf
          simp_rw [h_eq]
          have hbound' :
              ∀ t, 0 ≤ t →
                cosh t * exp (t - (z₀ / 2) * cosh t) ≤
                  exp (2 * t - (z₀ / 2) * exp t / 2) := by
            intro t ht
            have h_cosh_le : cosh t ≤ exp t := by
              rw [cosh_eq]
              have : exp (-t) ≤ exp t := exp_le_exp.mpr (by linarith)
              linarith
            have h_cosh_ge : cosh t ≥ exp t / 2 := by
              rw [cosh_eq]
              have : exp (-t) ≥ 0 := exp_nonneg _
              linarith
            calc cosh t * exp (t - (z₀ / 2) * cosh t)
                ≤ exp t * exp (t - (z₀ / 2) * cosh t) :=
                  mul_le_mul_of_nonneg_right h_cosh_le (exp_nonneg _)
              _ ≤ exp t * exp (t - (z₀ / 2) * (exp t / 2)) := by
                  apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
                  apply exp_le_exp.mpr
                  have :
                      -(z₀ / 2) * cosh t ≤ -(z₀ / 2) * (exp t / 2) :=
                    mul_le_mul_of_nonpos_left h_cosh_ge (by linarith)
                  linarith
              _ = exp (2 * t - (z₀ / 2) * exp t / 2) := by
                  rw [← exp_add]
                  ring_nf
          have h_exp_to_zero :
              Tendsto (fun t => exp (2 * t - (z₀ / 2) * exp t / 2)) atTop (nhds 0) := by
            apply tendsto_exp_atBot.comp
            have hexp_inf : Tendsto (fun t : ℝ => (z₀/2) * exp t / 2) atTop atTop := by
              apply Tendsto.atTop_div_const (by linarith : (0 : ℝ) < 2)
              exact Tendsto.const_mul_atTop hz₀' tendsto_exp_atTop
            have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
              have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
              simp only [pow_one] at h; convert h using 1; ext t; rw [exp_neg, div_eq_mul_inv]
            have h_scaled : Tendsto (fun t : ℝ => 4 / (z₀/2) * (t / exp t)) atTop (nhds 0) := by
              convert h_ratio.const_mul (4 / (z₀/2)) using 1; simp
            have h_shifted :
                Tendsto (fun t : ℝ => 4 / (z₀ / 2) * (t / exp t) - 1)
                  atTop (nhds (-1)) := by
              convert h_scaled.sub_const 1 using 1; simp
            have h_prod :
                Tendsto
                  (fun t : ℝ =>
                    ((z₀ / 2) * exp t / 2) * (4 / (z₀ / 2) * (t / exp t) - 1))
                  atTop atBot :=
              Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
            convert h_prod using 1; ext t; field_simp; ring
          have hpos : ∀ t, 0 ≤ cosh t * exp (t - (z₀ / 2) * cosh t) := fun t =>
            mul_nonneg (cosh_pos t).le (exp_nonneg _)
          exact squeeze_zero' (Eventually.of_forall hpos)
            (by
              filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
              exact hbound' t ht)
            h_exp_to_zero
        have h_ev : ∀ᶠ t in atTop, bound t ≤ exp (-1 * t) := by
          have h1 := (Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos).mono fun t ht => by
            simp only [Real.dist_eq, sub_zero] at ht; rw [abs_lt] at ht; exact ht.2
          filter_upwards [h1] with t ht
          have hgt : 0 < exp (-t) := exp_pos _
          have : bound t / exp (-t) < 1 := ht
          simp only [neg_mul, one_mul]; linarith [(div_lt_one hgt).mp this]
        filter_upwards [h_ev] with t ht
        simp only [hbound_def]
        rw [Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (cosh_pos t).le),
            Real.norm_of_nonneg (exp_nonneg _), one_mul]
        exact ht
      -- Extend from Ioi 1 to Ici 1 (differ by measure zero)
      exact h_Ioi.congr_set_ae Ioi_ae_eq_Ici.symm
  -- Integrand is continuous in z for each t
  · filter_upwards with t
    apply Continuous.continuousAt
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_id.neg.mul continuous_const)
    · exact continuous_const

/-- K₁ has exponential decay: K₁(z) ≤ (sinh(1) + 2) · exp(-z) for z ≥ 1.
    This bound is sufficient for proving integrability of the free covariance kernel.
    The proof uses the same technique as besselK1_mul_self_le but for z ≥ 1.
-/
lemma besselK1_asymptotic (z : ℝ) (hz : 1 ≤ z) :
    besselK1 z ≤ (sinh 1 + 2) * exp (-z) := by
  unfold besselK1
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh t with hf_def
  have hf_cont : Continuous f :=
    (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul continuous_cosh
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => mul_nonneg (exp_nonneg _) (cosh_pos t).le
  -- Split [0, ∞) = [0, 1] ∪ [1, ∞)
  have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · left; exact ⟨hx, h⟩
      · right; push Not at h; linarith
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  have hf_int_Icc : IntegrableOn f (Icc 0 1) :=
    hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hf_int_Ici1 : IntegrableOn f (Ici 1) := by
    -- Reuse the integrability argument from besselK1_pos
    have h_Ioi : IntegrableOn f (Ioi 0) volume := by
      apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
      rw [isBigO_iff]; use 1
      have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t)) atTop (nhds 0) := by
        have h_eq : ∀ t, f t / exp (-t) = cosh t * exp (t - z * cosh t) := fun t => by
          simp only [f]; field_simp; rw [mul_comm, ← exp_add]; ring_nf
        simp_rw [h_eq]
        have hbound :
            ∀ t, 0 ≤ t →
              cosh t * exp (t - z * cosh t) ≤ exp (2 * t - z * exp t / 2) := by
          intro t ht
          have h_cosh_le : cosh t ≤ exp t := by
            rw [cosh_eq]
            linarith [exp_le_exp.mpr (by linarith : -t ≤ t)]
          have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
          calc cosh t * exp (t - z * cosh t)
              ≤ exp t * exp (t - z * cosh t) :=
                mul_le_mul_of_nonneg_right h_cosh_le (exp_nonneg _)
            _ ≤ exp t * exp (t - z * (exp t / 2)) := by
                apply mul_le_mul_of_nonneg_left _ (exp_nonneg _); apply exp_le_exp.mpr
                linarith [mul_le_mul_of_nonpos_left h_cosh_ge (by linarith : -z ≤ 0)]
            _ = exp (2 * t - z * exp t / 2) := by rw [← exp_add]; ring_nf
        have h_exp_to_zero : Tendsto (fun t => exp (2 * t - z * exp t / 2)) atTop (nhds 0) := by
          apply tendsto_exp_atBot.comp
          have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop :=
            Tendsto.atTop_div_const (by linarith)
              (Tendsto.const_mul_atTop (by linarith : 0 < z) tendsto_exp_atTop)
          have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
            have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1; simp only [pow_one] at h
            convert h using 1; ext t; rw [exp_neg, div_eq_mul_inv]
          have h_scaled : Tendsto (fun t : ℝ => 4 / z * (t / exp t)) atTop (nhds 0) := by
            simpa using h_ratio.const_mul (4/z)
          have h_shifted : Tendsto (fun t : ℝ => 4 / z * (t / exp t) - 1) atTop (nhds (-1)) := by
            convert h_scaled.sub_const 1 using 1; simp
          have h_prod :
              Tendsto (fun t : ℝ => (z * exp t / 2) * (4 / z * (t / exp t) - 1))
                atTop atBot :=
            Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
          convert h_prod using 1; ext t; field_simp; ring
        refine squeeze_zero'
          (Eventually.of_forall fun t => mul_nonneg (cosh_pos t).le (exp_nonneg _))
          ?_ h_exp_to_zero
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact hbound t ht
      have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
        have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
          have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
          filter_upwards [this] with t ht; simp only [Real.dist_eq, sub_zero] at ht; exact ht
        filter_upwards [h1] with t ht
        have hgt : 0 < exp (-t) := exp_pos _
        rw [abs_lt] at ht
        have : f t < exp (-t) := (div_lt_one hgt).mp ht.2
        simp only [neg_mul, one_mul]; linarith
      filter_upwards [h_eventually_le] with t ht
      rw [Real.norm_of_nonneg (hf_nonneg t), Real.norm_of_nonneg (exp_nonneg _), one_mul]; exact ht
    exact h_Ioi.mono_set (fun x hx => by simp only [mem_Ioi, mem_Ici] at *; linarith)
  -- Part 1: ∫₀^1 f ≤ sinh(1) exp(-z) since f(t) ≤ exp(-z) cosh(t) and cosh(t) ≥ 1
  have h_part1 : ∫ t in Icc 0 1, f t ≤ sinh 1 * exp (-z) := by
    have h_pointwise : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ exp (-z) * cosh t := by
      intro t ⟨ht0, ht1⟩
      simp only [hf_def]
      have h1 : 1 ≤ cosh t := one_le_cosh t
      have h2 : -z * cosh t ≤ -z := by nlinarith
      exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr h2) (cosh_pos t).le
    have h_int_bound : ∫ t in Icc 0 1, f t ≤ ∫ t in Icc 0 1, exp (-z) * cosh t := by
      apply setIntegral_mono_on hf_int_Icc _ measurableSet_Icc h_pointwise
      exact (continuous_const.mul continuous_cosh).integrableOn_Icc
    have h_val : ∫ t in Icc 0 1, exp (-z) * cosh t = exp (-z) * sinh 1 := by
      -- Compute integral of exp(-z) * cosh on [0,1] via FTC for (exp(-z) * sinh)
      have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
        ((continuous_const.mul continuous_sinh).continuousOn)
        (fun x _ => by
          have hd : HasDerivAt (fun t => exp (-z) * sinh t) (exp (-z) * cosh x) x := by
            simpa using hasDerivAt_sinh x |>.const_mul (exp (-z))
          exact hd.hasDerivWithinAt)
        ((continuous_const.mul continuous_cosh).intervalIntegrable 0 1)
      simp only [Pi.mul_apply, sinh_zero, mul_zero, sub_zero] at h
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact h
    linarith
  -- Part 2: ∫₁^∞ f ≤ 2 exp(-z) using the same FTC argument as in besselK1_mul_self_le
  have h_part2 : ∫ t in Ici 1, f t ≤ 2 * exp (-z) := by
    set g : ℝ → ℝ := fun t => exp t * exp (-z * exp t / 2)
    set F : ℝ → ℝ := fun t => -2/z * exp (-z * exp t / 2)
    have hg_nonneg : ∀ t, 0 ≤ g t := fun t => mul_nonneg (exp_nonneg _) (exp_nonneg _)
    have h_bound' : ∀ t ≥ (1:ℝ), f t ≤ g t := by
      intro t ht; simp only [hf_def, g]
      have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
      have h_cosh_le : cosh t ≤ exp t := by
        rw [cosh_eq]
        linarith [exp_le_exp.mpr (by linarith : -t ≤ t)]
      calc exp (-z * cosh t) * cosh t
          ≤ exp (-z * (exp t / 2)) * cosh t := by
            apply mul_le_mul_of_nonneg_right _ (cosh_pos t).le; apply exp_le_exp.mpr; nlinarith
        _ ≤ exp (-z * (exp t / 2)) * exp t := mul_le_mul_of_nonneg_left h_cosh_le (exp_nonneg _)
        _ = exp t * exp (-z * exp t / 2) := by ring_nf
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := by
      intro t
      have h1 : HasDerivAt (fun s => -z * exp s / 2) (-z / 2 * exp t) t := by
        have := (hasDerivAt_exp t).const_mul (-z / 2); convert this using 1; funext; ring
      have h2 : HasDerivAt (fun s => exp (-z * exp s / 2))
          (exp (-z * exp t / 2) * (-z / 2 * exp t)) t :=
        (hasDerivAt_exp _).comp t h1
      simp only [g]; convert h2.const_mul (-2/z) using 1; field_simp
    have hF_cont : ContinuousWithinAt F (Ici 1) 1 := by
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul (continuous_exp.continuousAt.comp
        ((continuousAt_const.mul continuous_exp.continuousAt).div_const _))
    have hF_tendsto : Tendsto F atTop (nhds 0) := by
      have h1 : Tendsto (fun t => exp (-z * exp t / 2)) atTop (nhds 0) := by
        apply tendsto_exp_atBot.comp
        have h3 : Tendsto (fun t : ℝ => z / 2 * exp t) atTop atTop :=
          tendsto_exp_atTop.const_mul_atTop (by linarith : 0 < z / 2)
        have h4 : Tendsto (fun t => -(z / 2 * exp t)) atTop atBot :=
          Filter.tendsto_neg_atTop_atBot.comp h3
        convert h4 using 1; ext t; ring
      have h2 : Tendsto (fun t => (-2/z) * exp (-z * exp t / 2)) atTop (nhds ((-2/z) * 0)) :=
        h1.const_mul (-2/z)
      simp only [mul_zero] at h2
      convert h2 using 1
    have hg_int : IntegrableOn g (Ioi 1) := by
      apply integrableOn_Ioi_deriv_of_nonneg hF_cont
        (fun x _ => hF_deriv x) (fun x _ => hg_nonneg x) hF_tendsto
    have h_int_g : ∫ t in Ioi 1, g t = 2/z * exp (-z * exp 1 / 2) := by
      rw [integral_Ioi_of_hasDerivAt_of_tendsto hF_cont (fun x _ => hF_deriv x) hg_int hF_tendsto]
      simp only [F]; ring
    have hf_int_Ioi : IntegrableOn f (Ioi 1) := hf_int_Ici1.mono_set Ioi_subset_Ici_self
    have h_Ici_eq_Ioi : ∫ t in Ici 1, f t = ∫ t in Ioi 1, f t :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_mono : ∫ t in Ioi 1, f t ≤ ∫ t in Ioi 1, g t := by
      apply setIntegral_mono_on hf_int_Ioi hg_int measurableSet_Ioi
        (fun t ht => h_bound' t (le_of_lt ht))
    calc ∫ t in Ici 1, f t = ∫ t in Ioi 1, f t := h_Ici_eq_Ioi
      _ ≤ ∫ t in Ioi 1, g t := h_mono
      _ = 2/z * exp (-z * exp 1 / 2) := h_int_g
      _ ≤ 2 * exp (-z) := by
          have he : exp 1 > 0 := exp_pos 1
          have hz' : z > 0 := by linarith
          -- Key: exp 1 ≥ 2 from 1 + 1 ≤ exp 1 (using add_one_le_exp)
          have he2 : 2 ≤ exp (1:ℝ) := by linarith [add_one_le_exp (1:ℝ)]
          -- Therefore exp 1 / 2 ≥ 1, so z * exp 1 / 2 ≥ z, so -z * exp 1 / 2 ≤ -z
          have h_exp_bound : exp (-z * exp 1 / 2) ≤ exp (-z) := by
            apply exp_le_exp.mpr
            have h1 : z * exp 1 / 2 ≥ z * 2 / 2 := by nlinarith
            linarith
          -- 2/z ≤ 2 since z ≥ 1
          have hz_bound : 2 / z ≤ 2 := by
            have h1 : 2 ≤ 2 * z := by linarith
            exact (div_le_iff₀ hz').mpr h1
          calc 2/z * exp (-z * exp 1 / 2)
              ≤ 2/z * exp (-z) := by
                apply mul_le_mul_of_nonneg_left h_exp_bound
                positivity
            _ ≤ 2 * exp (-z) := by
                apply mul_le_mul_of_nonneg_right hz_bound
                positivity
  -- Combine using Ico for proper disjointness
  have h_union' : Ici (0 : ℝ) = Ico 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Ico]
    constructor
    · intro hx
      by_cases h : x < 1
      · left; exact ⟨hx, h⟩
      · right; push Not at h; exact h
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  have hf_int_Ico : IntegrableOn f (Ico 0 1) := hf_int_Icc.mono_set Ico_subset_Icc_self
  have h_disjoint : Disjoint (Ico (0:ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_Ico] at hx
    simp only [mem_Ici] at hx'
    linarith
  have h_Ico_eq_Icc : ∫ t in Ico 0 1, f t = ∫ t in Icc 0 1, f t :=
    setIntegral_congr_set Ico_ae_eq_Icc
  rw [h_union', setIntegral_union h_disjoint measurableSet_Ici hf_int_Ico hf_int_Ici1]
  calc (∫ t in Ico 0 1, f t) + (∫ t in Ici 1, f t)
      = (∫ t in Icc 0 1, f t) + (∫ t in Ici 1, f t) := by rw [h_Ico_eq_Icc]
    _ ≤ sinh 1 * exp (-z) + 2 * exp (-z) := add_le_add h_part1 h_part2
    _ = (sinh 1 + 2) * exp (-z) := by ring

private lemma besselK1_near_origin_tail_bound (z : ℝ) (hz : 0 < z)
    (f : ℝ → ℝ) (hf_def : f = fun t => exp (-z * cosh t) * cosh t)
    (hf_int_Ici : IntegrableOn f (Ici 1)) :
    z * ∫ t in Ici 1, f t ≤ 2 := by
  have h_bound : ∀ t ≥ 1, f t ≤ exp (-z * exp t / 2) * exp t := by
    intro t ht
    simp only [hf_def]
    have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
    have h_cosh_le : cosh t ≤ exp t := by
      rw [cosh_eq]
      linarith [exp_le_exp.mpr (by linarith : -t ≤ t)]
    have h_exp_eq : -z * (exp t / 2) = -z * exp t / 2 := by ring
    calc exp (-z * cosh t) * cosh t
        ≤ exp (-z * (exp t / 2)) * cosh t := by
          apply mul_le_mul_of_nonneg_right _ (cosh_pos t).le
          apply exp_le_exp.mpr
          have : -z * cosh t ≤ -z * (exp t / 2) := by nlinarith
          exact this
      _ = exp (-z * exp t / 2) * cosh t := by rw [h_exp_eq]
      _ ≤ exp (-z * exp t / 2) * exp t := by
          apply mul_le_mul_of_nonneg_left h_cosh_le (exp_nonneg _)
  set g : ℝ → ℝ := fun t => exp t * exp (-z * exp t / 2)
  set F : ℝ → ℝ := fun t => -2/z * exp (-z * exp t / 2)
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => mul_nonneg (exp_nonneg _) (exp_nonneg _)
  have h_bound' : ∀ t ≥ (1:ℝ), f t ≤ g t := by
    intro t ht; simp only [g]; rw [mul_comm]; exact h_bound t ht
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := by
    intro t
    have h1 : HasDerivAt (fun s => -z * exp s / 2) (-z / 2 * exp t) t := by
      have := (hasDerivAt_exp t).const_mul (-z / 2)
      convert this using 1; funext; ring
    have h2 : HasDerivAt (fun s => exp (-z * exp s / 2))
        (exp (-z * exp t / 2) * (-z / 2 * exp t)) t :=
      (hasDerivAt_exp _).comp t h1
    have h3 := h2.const_mul (-2/z)
    simp only [g] at *
    convert h3 using 1
    field_simp
  have hF_cont : ContinuousWithinAt F (Ici 1) 1 := by
    apply ContinuousAt.continuousWithinAt
    refine ContinuousAt.mul ?_ ?_
    · exact continuousAt_const
    · exact continuous_exp.continuousAt.comp
        ((continuousAt_const.mul continuous_exp.continuousAt).div_const _)
  have hF_tendsto : Tendsto F atTop (nhds 0) := by
    have h1 : Tendsto (fun t => exp (-z * exp t / 2)) atTop (nhds 0) := by
      apply tendsto_exp_atBot.comp
      have h3 : Tendsto (fun t : ℝ => z / 2 * exp t) atTop atTop :=
        tendsto_exp_atTop.const_mul_atTop (by linarith : 0 < z / 2)
      have h4 : Tendsto (fun t => -(z / 2 * exp t)) atTop atBot :=
        Filter.tendsto_neg_atTop_atBot.comp h3
      convert h4 using 1
      ext t; ring
    have h4 := h1.const_mul (-2/z)
    simp only [mul_zero] at h4
    exact h4
  have hg_int : IntegrableOn g (Ioi 1) := by
    apply integrableOn_Ioi_deriv_of_nonneg hF_cont
    · intro x _; exact hF_deriv x
    · intro x _; exact hg_nonneg x
    · exact hF_tendsto
  have h_int_g : ∫ t in Ioi 1, g t = -F 1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hF_cont (fun x _ => hF_deriv x) hg_int hF_tendsto]
    ring
  have h_neg_F1 : -F 1 = 2/z * exp (-z * exp 1 / 2) := by simp only [F]; ring
  have hf_int_Ioi : IntegrableOn f (Ioi 1) :=
    hf_int_Ici.mono_set (fun x hx => by exact mem_Ici_of_Ioi hx)
  have h_Ici_eq_Ioi : ∫ t in Ici 1, f t = ∫ t in Ioi 1, f t :=
    setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have h_mono : ∫ t in Ioi 1, f t ≤ ∫ t in Ioi 1, g t := by
    apply setIntegral_mono_on hf_int_Ioi hg_int measurableSet_Ioi
    intro t ht; exact h_bound' t (le_of_lt ht)
  calc z * ∫ t in Ici 1, f t
      = z * ∫ t in Ioi 1, f t := by rw [h_Ici_eq_Ioi]
    _ ≤ z * ∫ t in Ioi 1, g t := mul_le_mul_of_nonneg_left h_mono hz.le
    _ = z * (-F 1) := by rw [h_int_g]
    _ = z * (2/z * exp (-z * exp 1 / 2)) := by rw [h_neg_F1]
    _ = 2 * exp (-z * exp 1 / 2) := by field_simp
    _ ≤ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        rw [exp_le_one_iff]
        have he : exp 1 > 0 := exp_pos 1
        nlinarith
    _ = 2 := by ring

/-- For z ∈ (0, 1], we have z · K₁(z) ≤ cosh(1) + 2.
    This follows from splitting the integral at t = 1:
    - On [0,1]: z · ∫₀¹ exp(-z cosh t) cosh t dt ≤ z · cosh(1) ≤ cosh(1)
    - On [1,∞): z · ∫₁^∞ exp(-z cosh t) cosh t dt ≤ 2 (via exponential bound)
-/
lemma besselK1_mul_self_le (z : ℝ) (hz : 0 < z) (hz_le : z ≤ 1) :
    z * besselK1 z ≤ cosh 1 + 2 := by
  unfold besselK1
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh t with hf_def
  -- f is continuous and nonnegative
  have hf_cont : Continuous f :=
    (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul continuous_cosh
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => mul_nonneg (exp_nonneg _) (cosh_pos t).le
  -- Split [0,∞) = [0,1] ∪ [1,∞)
  have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · left; exact ⟨hx, h⟩
      · right; simp only [not_le] at h; linarith
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  -- Integrability on both parts
  have hf_int_Icc : IntegrableOn f (Icc 0 1) :=
    hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hf_int_Ici : IntegrableOn f (Ici 1) := by
    -- Use exponential decay bound from besselK1_pos proof
    have h_Ioi : IntegrableOn f (Ioi 0) volume := by
      apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
      rw [isBigO_iff]; use 1
      -- f(t)/exp(-t) → 0 as t → ∞ (super-exponential decay)
      have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t)) atTop (nhds 0) := by
        have h_eq : ∀ t, f t / exp (-t) = cosh t * exp (t - z * cosh t) := fun t => by
          simp only [f]; field_simp; rw [mul_comm, ← exp_add]; ring_nf
        simp_rw [h_eq]
        have hbound :
            ∀ t, 0 ≤ t →
              cosh t * exp (t - z * cosh t) ≤ exp (2 * t - z * exp t / 2) := by
          intro t ht
          have h_cosh_le : cosh t ≤ exp t := by
            rw [cosh_eq]
            linarith [exp_le_exp.mpr (by linarith : -t ≤ t)]
          have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
          calc cosh t * exp (t - z * cosh t)
              ≤ exp t * exp (t - z * cosh t) :=
                mul_le_mul_of_nonneg_right h_cosh_le (exp_nonneg _)
            _ ≤ exp t * exp (t - z * (exp t / 2)) := by
                apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
                apply exp_le_exp.mpr
                linarith [mul_le_mul_of_nonpos_left h_cosh_ge (by linarith : -z ≤ 0)]
            _ = exp (2 * t - z * exp t / 2) := by rw [← exp_add]; ring_nf
        have h_exp_to_zero : Tendsto (fun t => exp (2 * t - z * exp t / 2)) atTop (nhds 0) := by
          apply tendsto_exp_atBot.comp
          have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop :=
            Tendsto.atTop_div_const (by linarith)
              (Tendsto.const_mul_atTop hz tendsto_exp_atTop)
          have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
            have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1; simp only [pow_one] at h
            convert h using 1; ext t; rw [exp_neg, div_eq_mul_inv]
          have h_scaled : Tendsto (fun t : ℝ => 4 / z * (t / exp t)) atTop (nhds 0) := by
            simpa using h_ratio.const_mul (4 / z)
          have h_shifted : Tendsto (fun t : ℝ => 4 / z * (t / exp t) - 1) atTop (nhds (-1)) := by
            convert h_scaled.sub_const 1 using 1; simp
          have h_prod :
              Tendsto (fun t : ℝ => (z * exp t / 2) * (4 / z * (t / exp t) - 1))
                atTop atBot :=
            Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
          convert h_prod using 1; ext t; field_simp; ring
        refine squeeze_zero'
          (Eventually.of_forall fun t => mul_nonneg (cosh_pos t).le (exp_nonneg _))
          ?_ h_exp_to_zero
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact hbound t ht
      have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
        have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
          have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
          filter_upwards [this] with t ht; simp only [Real.dist_eq, sub_zero] at ht; exact ht
        filter_upwards [h1] with t ht
        have hgt : 0 < exp (-t) := exp_pos _
        rw [abs_lt] at ht
        have : f t < exp (-t) := (div_lt_one hgt).mp ht.2
        simp only [neg_mul, one_mul]; linarith
      filter_upwards [h_eventually_le] with t ht
      rw [Real.norm_of_nonneg (hf_nonneg t), Real.norm_of_nonneg (exp_nonneg _)]
      simp only [one_mul]; exact ht
    exact h_Ioi.mono_set (fun x hx => by simp only [mem_Ioi, mem_Ici] at *; linarith)
  -- Part 1: Bound on [0,1]
  have h_part1 : ∫ t in Icc 0 1, f t ≤ cosh 1 := by
    -- f(t) ≤ cosh(1) on [0,1] since exp(-z cosh t) ≤ 1 and cosh is increasing
    have h_pointwise : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ cosh 1 := by
      intro t ⟨ht0, ht1⟩
      simp only [hf_def]
      have h_exp_le : exp (-z * cosh t) ≤ 1 := by
        rw [exp_le_one_iff]; nlinarith [cosh_pos t]
      have h_cosh_le : cosh t ≤ cosh 1 := by
        -- cosh is increasing on [0,∞), so for 0 ≤ t ≤ 1, cosh t ≤ cosh 1
        rw [cosh_le_cosh]
        rw [abs_of_nonneg ht0, abs_of_pos (by linarith : (0:ℝ) < 1)]
        exact ht1
      calc exp (-z * cosh t) * cosh t ≤ 1 * cosh t := by nlinarith [cosh_pos t]
        _ ≤ cosh 1 := by simp [h_cosh_le]
    have h_meas_finite : volume (Icc (0:ℝ) 1) < ⊤ := measure_Icc_lt_top
    have h_meas_ne_top : volume (Icc (0:ℝ) 1) ≠ ⊤ := h_meas_finite.ne
    have h_const_int : IntegrableOn (fun _ => cosh 1) (Icc (0 : ℝ) 1) :=
      integrableOn_const (hs := h_meas_ne_top)
    have h_mono : ∫ t in Icc 0 1, f t ≤ ∫ _ in Icc (0:ℝ) 1, cosh 1 := by
      apply setIntegral_mono_on hf_int_Icc h_const_int measurableSet_Icc
      exact h_pointwise
    have h_const_val : ∫ _ in Icc (0:ℝ) 1, cosh 1 = cosh 1 := by
      rw [setIntegral_const, volume_real_Icc]
      simp only [sub_zero, max_eq_left (by linarith : (0:ℝ) ≤ 1), one_smul]
    linarith
  -- Part 2: Bound z * ∫₁^∞ f(t) dt ≤ 2
  -- Using cosh(t) ≤ exp(t) and cosh(t) ≥ exp(t)/2, we bound the integral
  have h_part2 : z * ∫ t in Ici 1, f t ≤ 2 :=
    besselK1_near_origin_tail_bound z hz f hf_def hf_int_Ici
  -- Combine: Use Ico instead of Icc for proper disjointness
  have h_union' : Ici (0 : ℝ) = Ico 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Ico]
    constructor
    · intro hx
      by_cases h : x < 1
      · left; exact ⟨hx, h⟩
      · right; simp only [not_lt] at h; exact h
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  have hf_int_Ico : IntegrableOn f (Ico 0 1) := hf_int_Icc.mono_set Ico_subset_Icc_self
  -- Disjointness: Ico 0 1 and Ici 1 are disjoint since x < 1 and x ≥ 1 are contradictory
  have h_disjoint : Disjoint (Ico (0:ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_Ico] at hx
    simp only [mem_Ici] at hx'
    linarith
  -- The integrals over Ico and Icc are equal (they differ by a null set)
  have h_Ico_eq_Icc : ∫ t in Ico 0 1, f t = ∫ t in Icc 0 1, f t :=
    setIntegral_congr_set Ico_ae_eq_Icc
  have h_part1' : z * ∫ t in Ico 0 1, f t ≤ cosh 1 := by
    have h_int_le : ∫ t in Ico 0 1, f t ≤ cosh 1 := by rw [h_Ico_eq_Icc]; exact h_part1
    have h_z_mul_le : z * ∫ t in Ico 0 1, f t ≤ z * cosh 1 :=
      mul_le_mul_of_nonneg_left h_int_le hz.le
    have h_z_cosh_le : z * cosh 1 ≤ 1 * cosh 1 := by nlinarith [cosh_pos (1:ℝ)]
    linarith
  have h_split : ∫ t in Ici 0, f t = (∫ t in Ico 0 1, f t) + (∫ t in Ici 1, f t) := by
    rw [h_union']
    exact setIntegral_union h_disjoint measurableSet_Ici hf_int_Ico hf_int_Ici
  have h_distrib :
      z * ∫ t in Ici 0, f t =
        (z * ∫ t in Ico 0 1, f t) + (z * ∫ t in Ici 1, f t) := by
    rw [h_split, mul_add]
  rw [h_distrib]
  exact add_le_add h_part1' h_part2

/-- Near-origin bound for K₁: K₁(z) ≤ (cosh(1) + 2)/z for z ∈ (0, 1].
    This follows from z · K₁(z) ≤ cosh(1) + 2 (proved in besselK1_mul_self_le).
-/
lemma besselK1_near_origin_bound (z : ℝ) (hz : 0 < z) (hz_small : z ≤ 1) :
    besselK1 z ≤ (cosh 1 + 2) / z := by
  have h_bound := besselK1_mul_self_le z hz hz_small
  -- z * K₁(z) ≤ cosh(1) + 2, so K₁(z) ≤ (cosh(1) + 2) / z
  exact (le_div_iff₀' hz).mpr h_bound

/-- The radial integrand r² K₁(mr) is integrable on (0, ∞) for m > 0.

    **Mathematical justification:**
    - Near 0: K₁(mr) ~ 1/(mr), so r² K₁(mr) ~ r/m, which is integrable near 0
    - At ∞: K₁(mr) ~ e^{-mr}/√(mr), so r² K₁(mr) decays exponentially

    This is a key ingredient for showing the free covariance kernel is L¹ in 4D.
-/
lemma radial_besselK1_integrable (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun r => r ^ 2 * besselK1 (m * r)) (Set.Ioi 0) volume := by
  -- Split (0, ∞) = (0, 1/m] ∪ (1/m, ∞)
  have h_split : Ioi (0 : ℝ) = Ioc 0 (1/m) ∪ Ioi (1/m) := by
    rw [Ioc_union_Ioi_eq_Ioi]
    positivity
  rw [h_split]
  apply IntegrableOn.union
  -- Part 1: Integrability on (0, 1/m]
  · -- Near origin: r² K₁(mr) ≤ r² * ((cosh 1 + 2)/(mr)) = (cosh 1 + 2)*r/m
    -- For r ∈ (0, 1/m], we have mr ∈ (0, 1], so K₁(mr) ≤ (cosh 1 + 2)/(mr)
    -- The function (cosh 1 + 2)*r/m is integrable on (0, 1/m]
    set C := cosh 1 + 2 with hC_def
    have hC_pos : 0 < C := by simp only [hC_def]; linarith [cosh_pos (1:ℝ)]
    -- Bound: r² K₁(mr) ≤ C * r / m for r ∈ (0, 1/m]
    have h_bound : ∀ r ∈ Ioc (0:ℝ) (1/m), r ^ 2 * besselK1 (m * r) ≤ C * r / m := by
      intro r ⟨hr_pos, hr_le⟩
      have hmr_pos : 0 < m * r := by positivity
      have hmr_le : m * r ≤ 1 := by
        calc m * r ≤ m * (1/m) := by nlinarith
          _ = 1 := by field_simp
      have h := besselK1_near_origin_bound (m * r) hmr_pos hmr_le
      calc r ^ 2 * besselK1 (m * r)
          ≤ r ^ 2 * (C / (m * r)) := by nlinarith [besselK1_pos (m * r) hmr_pos]
        _ = C * r / m := by field_simp [ne_of_gt hr_pos, ne_of_gt hm]
    -- The bounding function C*r/m is integrable on (0, 1/m]
    have h_bound_int : IntegrableOn (fun r => C * r / m) (Ioc 0 (1/m)) := by
      have h_cont : Continuous (fun r : ℝ => C * r / m) := by continuity
      exact h_cont.integrableOn_Ioc
    -- Key insight: the function is continuous and bounded by an integrable function
    -- Use Integrable.mono' with the bound
    have hf_meas :
        AEStronglyMeasurable
          (fun r => r ^ 2 * besselK1 (m * r)) (volume.restrict (Ioc 0 (1 / m))) := by
      -- besselK1 ∘ (m * ·) is continuous on (0, ∞); here `m > 0`.
      have hcont : ContinuousOn (fun r => r ^ 2 * besselK1 (m * r)) (Ioi 0) := by
        apply ContinuousOn.mul (continuous_pow 2).continuousOn
        apply besselK1_continuousOn.comp (continuous_const_mul m).continuousOn
        intro r hr; simp only [mem_Ioi] at hr ⊢; exact mul_pos hm hr
      -- Ioc 0 (1/m) ⊆ Ioi 0 for the restriction
      have hsub : Ioc 0 (1/m) ⊆ Ioi 0 := fun r ⟨hr, _⟩ => hr
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc
    have h_nonneg :
        ∀ r ∈ Ioc (0 : ℝ) (1 / m), 0 ≤ r ^ 2 * besselK1 (m * r) := fun r ⟨hr_pos, _⟩ =>
      mul_nonneg (sq_nonneg r) (besselK1_pos (m * r) (by positivity)).le
    have h_norm_bound :
        ∀ᵐ r ∂(volume.restrict (Ioc 0 (1 / m))),
          ‖r ^ 2 * besselK1 (m * r)‖ ≤ C * r / m := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      apply Eventually.of_forall
      intro r hr
      rw [Real.norm_of_nonneg (h_nonneg r hr)]
      exact h_bound r hr
    exact Integrable.mono' h_bound_int hf_meas h_norm_bound
  -- Part 2: Integrability on (1/m, ∞)
  · -- At infinity: use besselK1_asymptotic for exponential decay
    -- For r > 1/m, we have mr > 1, so K₁(mr) ≤ (sinh 1 + 2) exp(-mr)
    set C := sinh 1 + 2 with hC_def
    have hC_pos : 0 < C := by
      simp only [hC_def]
      nlinarith [sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < 1)]
    -- Bound: r² K₁(mr) ≤ C * r² * exp(-mr) for r > 1/m
    have h_bound :
        ∀ r ∈ Ioi (1 / m : ℝ),
          r ^ 2 * besselK1 (m * r) ≤ C * r ^ 2 * exp (-m * r) := by
      intro r hr
      have hmr_ge : m * r ≥ 1 := by
        simp only [mem_Ioi] at hr
        have h1 : m * (1/m) = 1 := by field_simp
        have h2 : m * r > m * (1/m) := mul_lt_mul_of_pos_left hr hm
        linarith
      have hK1_bound := besselK1_asymptotic (m * r) hmr_ge
      calc r ^ 2 * besselK1 (m * r)
          ≤ r ^ 2 * (C * exp (-(m * r))) := by
            apply mul_le_mul_of_nonneg_left hK1_bound (sq_nonneg r)
        _ = C * r ^ 2 * exp (-m * r) := by ring_nf
    -- The bounding function C * r² * exp(-mr) is integrable on (1/m, ∞)
    -- r² exp(-mr) is integrable because polynomial growth is beaten by exponential decay
    have h_bound_int : IntegrableOn (fun r => C * r ^ 2 * exp (-m * r)) (Ioi (1/m)) := by
      -- Use integrable_of_isBigO_exp_neg: polynomial times exponential is integrable
      have h_int' : IntegrableOn (fun r => r ^ 2 * exp (-m * r)) (Ioi (1/m)) := by
        -- r² * exp(-mr) = O(exp(-m/2 * r)) since r² * exp(-mr/2) → 0
        apply integrable_of_isBigO_exp_neg (by linarith : 0 < m/2)
        · -- ContinuousOn (fun r => r² * exp(-mr)) (Ici (1/m))
          apply ContinuousOn.mul (continuous_pow 2).continuousOn
          have hcont : Continuous (fun r : ℝ => exp (-m * r)) := by continuity
          exact hcont.continuousOn
        · -- r² * exp(-mr) = O(exp(-m/2 * r)) at infinity
          -- First establish that r² * exp(-mr/2) → 0, so eventually r² * exp(-mr/2) ≤ 1
          have h_tendsto := tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
          -- Scale: (m/2 * r)² * exp(-(m/2)*r) → 0, so r² * exp(-(m/2)*r) → 0
          have h_scale : Tendsto (fun r => r ^ 2 * exp (-(m/2) * r)) atTop (nhds 0) := by
            have hm2 : 0 < m / 2 := by linarith
            have h1 := h_tendsto.comp (tendsto_id.const_mul_atTop hm2)
            -- Simplify h1 from composition form
            simp only [Function.comp_def, id] at h1
            -- (m/2 * r)² * exp(-(m/2 * r)) = (m/2)² * r² * exp(-(m/2)*r)
            have h2 : (fun r => (m/2 * r) ^ 2 * exp (-(m/2 * r))) =
                      (fun r => (m/2)^2 * (r ^ 2 * exp (-(m/2) * r))) := by
              ext r; ring_nf
            rw [h2] at h1
            have h3 : (m/2)^2 ≠ 0 := by positivity
            -- Use tendsto_const_smul_iff₀: if c ≠ 0 then (c • f → c • a) ↔ (f → a)
            -- In ℝ, c • x = c * x, so this applies
            have h1' :
                Tendsto (fun r => (m / 2) ^ 2 • (r ^ 2 * exp (-(m / 2) * r)))
                  atTop (nhds ((m / 2) ^ 2 • 0)) := by
              simp only [smul_eq_mul, mul_zero]; exact h1
            rw [tendsto_const_smul_iff₀ h3] at h1'
            exact h1'
          -- Eventually r² * exp(-mr/2) ≤ 1
          have h_ev : ∀ᶠ r in atTop, r ^ 2 * exp (-(m/2) * r) ≤ 1 :=
            (Metric.tendsto_nhds.mp h_scale 1 one_pos).mono fun r h => by
              simp only [Real.dist_eq, sub_zero] at h; rw [abs_lt] at h; linarith
          -- Now prove the IsBigO
          apply Asymptotics.IsBigO.of_bound 1
          filter_upwards [eventually_ge_atTop (1:ℝ), h_ev] with r hr h_le
          rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg r) (exp_nonneg _)), one_mul,
              Real.norm_of_nonneg (exp_nonneg _)]
          -- r² * exp(-mr) = (r² * exp(-mr/2)) * exp(-mr/2) ≤ 1 * exp(-mr/2)
          have hexp : exp (-m * r) = exp (-(m/2) * r) * exp (-(m/2) * r) := by
            rw [← exp_add]; congr 1; ring
          calc r ^ 2 * exp (-m * r)
              = r ^ 2 * (exp (-(m/2) * r) * exp (-(m/2) * r)) := by rw [hexp]
            _ = (r ^ 2 * exp (-(m/2) * r)) * exp (-(m/2) * r) := by ring
            _ ≤ 1 * exp (-(m/2) * r) := by nlinarith [exp_pos (-(m/2) * r)]
            _ = exp (-(m/2) * r) := one_mul _
      have h_eq : (fun r => C * r ^ 2 * exp (-m * r)) = (fun r => C * (r ^ 2 * exp (-m * r))) := by
        ext r; ring
      rw [h_eq]
      exact h_int'.const_mul C
    -- The function r² K₁(mr) is ae strongly measurable
    have hf_meas :
        AEStronglyMeasurable
          (fun r => r ^ 2 * besselK1 (m * r)) (volume.restrict (Ioi (1 / m))) := by
      -- besselK1 ∘ (m * ·) is continuous on (0, ∞); here `m > 0`.
      have hcont : ContinuousOn (fun r => r ^ 2 * besselK1 (m * r)) (Ioi 0) := by
        apply ContinuousOn.mul (continuous_pow 2).continuousOn
        apply besselK1_continuousOn.comp (continuous_const_mul m).continuousOn
        intro r hr; simp only [mem_Ioi] at hr ⊢; exact mul_pos hm hr
      -- Ioi (1/m) ⊆ Ioi 0 for the restriction
      have hsub : Ioi (1 / m) ⊆ Ioi 0 := fun r hr => by
        simp only [mem_Ioi] at hr ⊢
        linarith [one_div_pos.mpr hm]
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioi
    have h_nonneg : ∀ r ∈ Ioi (1/m : ℝ), 0 ≤ r ^ 2 * besselK1 (m * r) := by
      intro r hr
      apply mul_nonneg (sq_nonneg r)
      have hr' : 0 < r := by simp only [mem_Ioi] at hr; linarith [one_div_pos.mpr hm]
      exact (besselK1_pos (m * r) (mul_pos hm hr')).le
    have h_norm_bound :
        ∀ᵐ r ∂(volume.restrict (Ioi (1 / m))),
          ‖r ^ 2 * besselK1 (m * r)‖ ≤ C * r ^ 2 * exp (-m * r) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply Eventually.of_forall
      intro r hr
      rw [Real.norm_of_nonneg (h_nonneg r hr)]
      exact h_bound r hr
    exact Integrable.mono' h_bound_int hf_meas h_norm_bound

/-- Symmetry lemma: the full-line integral of exp(-u) * exp(-z cosh u) equals
    twice the half-line cosh integral, which is 2 * K₁(z).

    ∫_{-∞}^∞ exp(-u) * exp(-z cosh u) du = 2 ∫_0^∞ cosh(u) * exp(-z cosh u) du

    This follows from splitting at 0 and using cosh(-u) = cosh(u).
-/
lemma bessel_symmetry_integral (z : ℝ) (hz : 0 < z) :
    ∫ u : ℝ, exp (-u) * exp (-z * cosh u) = 2 * besselK1 z := by
  -- Integrability conditions (both decay super-exponentially as u → ∞)
  have hg_int : IntegrableOn (fun u => exp u * exp (-z * cosh u)) (Ioi 0) := by
    -- g(u) = exp(u) * exp(-z*cosh(u)) decays super-exponentially
    -- Use integrable_of_isBigO_exp_neg with b = 1
    apply integrable_of_isBigO_exp_neg (a := 0) (b := 1)
    · exact one_pos
    · -- ContinuousOn
      apply ContinuousOn.mul
      · exact continuous_exp.continuousOn
      · exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn
    · -- IsBigO: need to show exp(u)*exp(-z*cosh(u)) = O(exp(-u)) at atTop
      -- Key: for u large enough, z*cosh(u) ≥ 2u (since cosh grows exponentially)
      apply Asymptotics.IsBigO.of_bound 1
      -- Use cutoff max(4, 8/z) - for u ≥ 4, we have exp(u) ≥ u²/2
      filter_upwards [eventually_ge_atTop (max 4 (8/z))] with u hu
      simp only [Real.norm_eq_abs, one_mul, neg_mul]
      rw [abs_of_pos (mul_pos (exp_pos _) (exp_pos _))]
      rw [abs_of_pos (exp_pos _)]
      -- Goal: exp(u)*exp(-z*cosh(u)) ≤ exp(-u), i.e., 2u ≤ z*cosh(u)
      have hu4 : u ≥ 4 := le_trans (le_max_left _ _) hu
      have hu8z : u ≥ 8/z := le_trans (le_max_right _ _) hu
      have hzu : z * u ≥ 8 := by
        calc z * u ≥ z * (8 / z) := by nlinarith [hu8z]
          _ = 8 := by field_simp
      have h_cosh_eq : cosh u = (exp u + exp (-u)) / 2 := cosh_eq u
      have h_cosh_lower : cosh u ≥ exp u / 2 := by
        rw [h_cosh_eq]; have := exp_pos (-u); linarith
      have h_cosh_pos : 0 < cosh u := cosh_pos u
      -- Key bound: exp(u) ≥ u²/2 for u ≥ 4
      -- Proof: exp(4) > 49 > 8 = 4²/2, and exp(u) - u²/2 is increasing for u ≥ 4
      have h_exp_ge_usq : exp u ≥ u^2 / 2 := by
        have h_exp1 : exp 1 > 2.7 := by have := Real.exp_one_gt_d9; linarith
        have h_exp2 : exp 2 > 7 := by
          have h : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
          nlinarith [h]
        have h_exp4 : exp 4 > 49 := by
          have h : exp 4 = exp 2 * exp 2 := by rw [← exp_add]; norm_num
          nlinarith [h]
        -- exp(u) - u²/2 is strictly increasing for u ≥ 4 (derivative = exp(u) - u > 0)
        have h_strict_mono : StrictMonoOn (fun v => exp v - v^2 / 2) (Set.Ici 4) := by
          apply strictMonoOn_of_deriv_pos (convex_Ici 4)
          · exact (continuous_exp.sub (continuous_pow 2 |>.div_const 2)).continuousOn
          · intro x hx
            simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
            have hx4 : x > 4 := hx
            -- Derivative of exp(v) - v²/2 is exp(v) - v
            have hderiv : deriv (fun v => exp v - v^2 / 2) x = exp x - x := by
              have hd1 : DifferentiableAt ℝ (fun v => exp v) x := differentiableAt_exp
              have hd2 : DifferentiableAt ℝ (fun v => v ^ 2 / 2) x :=
                (differentiableAt_pow 2).div_const 2
              have heq : (fun v => exp v - v^2 / 2) = (fun v => exp v) - (fun v => v^2 / 2) := by
                ext v; simp [sub_eq_add_neg]
              rw [heq, deriv_sub hd1 hd2, deriv_div_const]
              simp only [Real.deriv_exp]
              -- deriv (fun v => v^2) x = 2 * x
              have hpow : deriv (fun v : ℝ => v ^ (2 : ℕ)) x = (2 : ℝ) * x ^ (2 - 1) :=
                deriv_pow_field 2
              simp only [pow_one, Nat.add_one_sub_one] at hpow
              rw [hpow]; ring
            rw [hderiv]
            -- Need exp(x) - x > 0 for x > 4. Use exp(x) > x for all x > 0.
            -- exp(x) ≥ 1 + x, so exp(x) - x ≥ 1 > 0
            have := add_one_le_exp x
            linarith
        by_cases hu4eq : u = 4
        · simp only [hu4eq]; linarith [h_exp4]
        · have hug4 : u > 4 := lt_of_le_of_ne hu4 (Ne.symm hu4eq)
          have h_at_4 : exp 4 - (4 : ℝ)^2 / 2 > 0 := by norm_num; linarith [h_exp4]
          have := h_strict_mono (Set.self_mem_Ici) (le_of_lt hug4) hug4
          linarith
      -- Now derive the main bound: z*cosh(u) ≥ 2u
      -- z*cosh(u) ≥ z*exp(u)/2 ≥ z*(u²/2)/2 = z*u²/4
      -- Since z*u ≥ 8: z*u²/4 = (z*u/4)*u ≥ 2*u (when z*u/4 ≥ 2, i.e., z*u ≥ 8)
      have h_cosh_bound : 2 * u ≤ z * cosh u := by
        have h1 : z * cosh u ≥ z * (exp u / 2) := by nlinarith [h_cosh_lower]
        have h2 : z * (exp u / 2) ≥ z * (u^2 / 2) / 2 := by nlinarith [h_exp_ge_usq, hz]
        have h3 : z * (u^2 / 2) / 2 = z * u^2 / 4 := by ring
        have h4 : z * u^2 / 4 = (z * u / 4) * u := by ring
        have h5 : z * u / 4 ≥ 2 := by linarith [hzu]
        have h6 : (z * u / 4) * u ≥ 2 * u := by nlinarith [hu4]
        linarith
      have h_ineq : u - z * cosh u ≤ -u := by linarith
      calc exp u * exp (-(z * cosh u))
          = exp (u + (-(z * cosh u))) := by rw [← exp_add]
        _ = exp (u - z * cosh u) := by ring_nf
        _ ≤ exp (-u) := exp_le_exp.mpr h_ineq
  have hf_int_Ioi : IntegrableOn (fun u => exp (-u) * exp (-z * cosh u)) (Ioi 0) := by
    -- f(u) = exp(-u) * exp(-z*cosh(u)) ≤ exp(-u) since exp(-z*cosh(u)) ≤ 1 (z,cosh > 0)
    apply Integrable.mono' (g := fun u => exp (-u))
    · -- exp(-u) is integrable on (0, ∞)
      exact integrableOn_exp_neg_Ioi 0
    · -- Measurability
      have hcont : Continuous (fun u => exp (-u) * exp (-z * cosh u)) := by
        apply Continuous.mul
        · exact continuous_exp.comp continuous_neg
        · apply Continuous.comp continuous_exp
          -- -z * cosh u = (-z) * cosh u, where -z is a constant
          exact continuous_const.mul continuous_cosh
      exact hcont.aestronglyMeasurable
    · -- Bound: |f(u)| ≤ exp(-u)
      apply ae_of_all
      intro u
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (mul_pos (exp_pos _) (exp_pos _))]
      have h_cosh_pos : cosh u > 0 := cosh_pos u
      have h_exp_bound : exp (-z * cosh u) ≤ 1 := by
        rw [exp_le_one_iff]
        nlinarith [hz, h_cosh_pos]
      calc exp (-u) * exp (-z * cosh u) ≤ exp (-u) * 1 := by nlinarith [exp_pos (-u)]
        _ = exp (-u) := mul_one _
  have hf_int_Iic : IntegrableOn (fun u => exp (-u) * exp (-z * cosh u)) (Iic 0) := by
    -- hg_int.comp_neg: g(-u) integrable on -Ioi 0, where g(u) = exp(u) * exp(-z*cosh(u))
    -- g(-u) = exp(-u) * exp(-z*cosh(-u)) = exp(-u) * exp(-z*cosh(u)) = f(u) (since cosh is even)
    have h1 : IntegrableOn (fun u => exp (-u) * exp (-z * cosh (-u))) (-(Ioi (0 : ℝ))) :=
      hg_int.comp_neg
    -- Use cosh(-u) = cosh(u)
    have h2 : IntegrableOn (fun u => exp (-u) * exp (-z * cosh u)) (-(Ioi (0 : ℝ))) := by
      simp only [cosh_neg] at h1
      exact h1
    -- -(Ioi 0) = Iio 0
    have hIio_eq : -(Ioi (0 : ℝ)) = Iio 0 := by
      ext x; simp only [Set.mem_neg, Set.mem_Ioi, Set.mem_Iio]; constructor <;> intro h <;> linarith
    rw [hIio_eq] at h2
    -- Iic 0 and Iio 0 are a.e. equal
    exact h2.congr_set_ae Iio_ae_eq_Iic.symm
  -- 1. Split the integral over ℝ into (-∞, 0] and (0, ∞) using
  -- intervalIntegral.integral_Iic_add_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hf_int_Iic hf_int_Ioi]
  -- 2. Transform the negative part (Iic 0) using u ↦ -u
  --    ∫_{-∞}^0 f(u) du = ∫_0^∞ f(-u) du = ∫_0^∞ g(u) du.
  --    This uses `u → -u` and `cosh(-u) = cosh(u)`.
  have h_neg_part : ∫ u in Iic 0, exp (-u) * exp (-z * cosh u) =
                    ∫ u in Ioi 0, exp u * exp (-z * cosh u) := by
    have h := integral_comp_neg_Iic (f := fun u => exp u * exp (-z * cosh u)) 0
    simp only [neg_zero] at h
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro u _
    simp only [cosh_neg]
  -- 3. Substitute and combine
  rw [h_neg_part, ← MeasureTheory.integral_add hg_int hf_int_Ioi]
  -- Combine integrands: (e^u + e^-u) * exp(-z cosh u) = 2 cosh(u) * exp(-z cosh u)
  have h_combine : ∫ u in Ioi 0, exp u * exp (-z * cosh u) + exp (-u) * exp (-z * cosh u) =
      ∫ u in Ioi 0, 2 * cosh u * exp (-z * cosh u) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only
    rw [cosh_eq]; ring
  rw [h_combine]
  -- Factor out the 2
  have h_factor : ∫ u in Ioi 0, 2 * cosh u * exp (-z * cosh u) =
      2 * ∫ u in Ioi 0, cosh u * exp (-z * cosh u) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _; ring
  rw [h_factor]
  -- Match with besselK1 definition (which uses Ici 0 = [0, ∞))
  have h_Ioi_Ici : ∫ u in Ioi 0, cosh u * exp (-z * cosh u) =
      ∫ u in Ici 0, cosh u * exp (-z * cosh u) := setIntegral_congr_set Ioi_ae_eq_Ici
  rw [h_Ioi_Ici]
  unfold besselK1
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro u _; ring

/-- Key identity connecting the Schwinger proper-time integral to K₁:
    ∫₀^∞ t^{-2} exp(-m²t - r²/(4t)) dt = (4m/r) · K₁(mr)

    This is proven directly via the substitution t = (r/(2m)) exp(u),
    which transforms the integral to the cosh representation of K₁.
-/
lemma schwingerIntegral_eq_besselK1 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t^2) * exp (-m^2 * t - r^2 / (4 * t)) =
    (4 * m / r) * besselK1 (m * r) := by
  /-
  Direct proof via substitution t = (r/(2m)) exp(u):

  With this substitution:
  - dt = (r/(2m)) exp(u) du
  - t ranges (0, ∞) as u ranges (-∞, ∞)
  - m²t + r²/(4t) = m²(r/(2m))exp(u) + r²/(4(r/(2m))exp(u))
                  = (mr/2)(exp(u) + exp(-u)) = mr cosh(u)
  - (1/t²) dt = (2m/r)² exp(-2u) · (r/(2m)) exp(u) du = (2m/r) exp(-u) du

  Therefore:
  ∫₀^∞ t⁻² exp(-m²t - r²/(4t)) dt = (2m/r) ∫_{-∞}^∞ exp(-u) exp(-mr cosh u) du
                                   = (2m/r) · 2 K₁(mr)    [by symmetry lemma]
                                   = (4m/r) K₁(mr)
  -/
  let z := m * r
  have hz : 0 < z := mul_pos hm hr
  -- This equals `(2m/r) * (full-line integral)`, hence `(4m/r) * K₁(mr)`.
  have h_factor : (4 * m / r) = (2 * m / r) * 2 := by ring
  rw [h_factor, mul_assoc, ← bessel_symmetry_integral z hz]
  -- It remains to relate the proper-time integral to the full-line cosh integral.
  -- Define the substitution φ(u) = (r/(2m)) exp(u)
  let c := r / (2 * m)
  have hc : 0 < c := by simp only [c]; positivity
  -- The key is to use integral_image_eq_integral_abs_deriv_smul for the exponential map
  -- φ : ℝ → (0, ∞) given by φ(u) = c * exp(u) is a diffeomorphism
  -- For now, we use the algebraic verification that both sides match
  -- The substitution proof requires integral_image_eq_integral_deriv_smul_of_monotoneOn
  -- which we apply to the strictly monotone function φ(u) = c * exp(u)
  -- Step 1: Show the integrand transforms correctly
  have h_transform : ∀ u : ℝ,
      (c * exp u) * ((1 / (c * exp u)^2) * exp (-(m^2 * (c * exp u)) - r^2 / (4 * (c * exp u)))) =
      (2 * m / r) * (exp (-u) * exp (-z * cosh u)) := by
    intro u
    simp only [c, z]
    have hm_ne : m ≠ 0 := hm.ne'
    have hr_ne : r ≠ 0 := hr.ne'
    have he : exp u ≠ 0 := (exp_pos u).ne'
    -- Verify: m² * c * exp(u) + r² / (4 * c * exp(u)) = mr * cosh(u)
    have h_sum : m^2 * (r / (2 * m) * exp u) + r^2 / (4 * (r / (2 * m) * exp u)) =
        m * r * cosh u := by
      have h1 : exp u * exp (-u) = 1 := by rw [exp_neg]; exact mul_inv_cancel₀ he
      field_simp
      rw [cosh_eq]
      ring_nf
      rw [h1]
      ring
    -- Verify: c * exp(u) / (c * exp(u))² = (2m/r) * exp(-u)
    have h_jacobian : r / (2 * m) * exp u / (r / (2 * m) * exp u) ^ 2 =
        2 * m / r * exp (-u) := by
      field_simp
      rw [exp_neg]
      field_simp
    -- The key algebraic calculation
    have ht : r / (2 * m) * exp u ≠ 0 := by positivity
    calc (r / (2 * m) * exp u) * (1 / (r / (2 * m) * exp u) ^ 2 *
            exp (-(m ^ 2 * (r / (2 * m) * exp u)) - r ^ 2 / (4 * (r / (2 * m) * exp u))))
        = (r / (2 * m) * exp u / (r / (2 * m) * exp u) ^ 2) *
            exp (-(m ^ 2 * (r / (2 * m) * exp u) + r ^ 2 / (4 * (r / (2 * m) * exp u)))) := by
          have : -(m ^ 2 * (r / (2 * m) * exp u)) - r ^ 2 / (4 * (r / (2 * m) * exp u)) =
              -(m ^ 2 * (r / (2 * m) * exp u) + r ^ 2 / (4 * (r / (2 * m) * exp u))) := by ring
          rw [this]
          field_simp
      _ = (2 * m / r * exp (-u)) * exp (-(m * r * cosh u)) := by rw [h_jacobian, h_sum]
      _ = 2 * m / r * (exp (-u) * exp (-(m * r) * cosh u)) := by ring_nf
  -- Step 2: Apply the change of variables formula
  -- The substitution φ(u) = c exp(u) is strictly monotone and maps ℝ onto (0, ∞)
  -- We'll use bounded interval approximation
  -- Define the integrand on the t-side
  let g : ℝ → ℝ := fun t => 1 / t ^ 2 * exp (-m ^ 2 * t - r ^ 2 / (4 * t))
  -- Key: both integrals are well-defined
  -- LHS is integrable on Ioi 0 (follows from the decay of the integrand)
  -- RHS is integrable on ℝ (by bessel_symmetry_integral's proof)
  -- For bounded intervals, change of variables gives:
  -- ∫_{c*exp(a)}^{c*exp(b)} g(t) dt = ∫_a^b (c*exp(u)) * g(c*exp(u)) du
  -- Taking a → -∞, b → ∞ gives the result
  -- Using h_transform, the RHS integrand is (2m/r) * exp(-u) * exp(-z * cosh u)
  -- So ∫_ℝ (c*exp(u)) * g(c*exp(u)) du = (2m/r) * ∫_ℝ exp(-u) * exp(-z * cosh u) du
  -- Apply change of variables via bounded interval limits
  have h_cov : ∫ t in Ioi 0, g t = ∫ u, (c * exp u) * g (c * exp u) := by
    -- This is the key step: φ(u) = c * exp(u) maps ℝ bijectively to Ioi 0
    -- Using the Jacobian formula with φ'(u) = c * exp(u)
    let φ := fun u => c * exp u
    have hφ_mono : StrictMono φ := by
      intro a b hab
      exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr hab) hc
    have hφ_surj : φ '' Set.univ = Ioi 0 := by
      ext t
      simp only [Set.mem_image, Set.mem_univ, true_and, mem_Ioi, φ]
      constructor
      · rintro ⟨u, rfl⟩
        exact mul_pos hc (exp_pos u)
      · intro ht
        use Real.log (t / c)
        rw [exp_log (by positivity : t / c > 0)]
        field_simp
    have hφ_deriv : ∀ u ∈ Set.univ, HasDerivWithinAt φ (c * exp u) Set.univ u := by
      intro u _
      exact ((hasDerivAt_exp u).const_mul c).hasDerivWithinAt
    -- Apply the change of variables formula
    calc ∫ t in Ioi 0, g t
        = ∫ t in φ '' Set.univ, g t := by rw [hφ_surj]
      _ = ∫ u in Set.univ, (c * exp u) • g (φ u) :=
          integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
            hφ_deriv (hφ_mono.monotone.monotoneOn Set.univ) g
      _ = ∫ u, (c * exp u) * g (c * exp u) := by
          rw [setIntegral_univ]; simp only [smul_eq_mul, φ]
  rw [h_cov]
  -- Now apply h_transform to simplify the integrand
  have h_eq : ∫ u, (c * exp u) * g (c * exp u) =
      ∫ u, (2 * m / r) * (exp (-u) * exp (-z * cosh u)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    simp only [g]
    -- The expressions differ only in parenthesization: -(m^2 * t) vs -m^2 * t
    convert h_transform u using 2
    congr 1
    ring_nf
  rw [h_eq, integral_const_mul]
