/-
Copyright (c) 2026 seb488, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: seb488, Aristotle
-/
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import LeanPool.LeanComplexAnalysis.Harmonic.PoissonIntegral

/-!
# Harnack's inequality

## Main Results

Theorem `harnack_ineq`:

A positive harmonic function `u` on the unit disc satisfies the inequalities
    `(1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖)`
for all `z` in the unit disc.
-/

namespace LeanPool.LeanComplexAnalysis

open  Complex InnerProductSpace Metric Set Real

lemma non_neg_boundary
    (u : ℂ → ℝ) (t : ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (hc : ContinuousOn u (closedBall 0 1)) :
    0 ≤ u (exp (t * I)) := by
  have h_boundary : Filter.Tendsto (fun r : ℝ => u (r * exp (t * I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (u (exp (t * I)))) := by
      have h_cont : ContinuousOn (fun r : ℝ => u (r * exp (t * I))) (Set.Icc 0 1) := by
        refine hc.comp ?_ ?_
        · fun_prop
        · norm_num [Set.MapsTo, norm_exp]
          exact fun x hx₁ hx₂ => abs_le.mpr ⟨by linarith, by linarith⟩
      have := h_cont 1 (by norm_num)
      simpa using this.tendsto.mono_left <| nhdsWithin_mono _ <| Set.Ioo_subset_Icc_self
  have h_boundary : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < u (r * exp (t * I)) := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr using h_pos _ <| by
        simpa [abs_of_nonneg hr.1.le, norm_exp] using hr.2
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› (
      Filter.eventually_of_mem h_boundary fun x hx => le_of_lt hx)

lemma harnack_ineq_cont_normalized_upper
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_f_zero : u 0 = 1)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    u z ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
  have h_poisson : u z = (1 / (2 * π)) * ∫ t in 0..(2 * π),
    (1 - ‖z‖^2) / ‖(exp (t * Complex.I)) - z‖^2 * u (exp (t * Complex.I)) := by
    convert poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc h_harmonic hc hz
      using 1;
  have h_max : ∫ t in (0 : ℝ)..(2 * π),
    (1 - ‖z‖^2) / ‖(exp (t * Complex.I)) - z‖^2 * u (exp (t * Complex.I)) ≤
    ∫ t in (0 : ℝ)..(2 * π), (1 - ‖z‖^2) / (1 - ‖z‖)^2 * u (exp (t * Complex.I)) := by
    refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_
    · positivity
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.div ?_ ?_ ?_
        · exact continuousOn_const
        · fun_prop
        · intro x _
          apply pow_ne_zero
          intro heq
          rw [norm_eq_zero] at heq
          have hz_eq : z = cexp (↑x * I) := by
            grind only
          have hz_norm : ‖z‖ = 1 := by
            simp [hz_eq]
          rw [mem_ball_zero_iff] at hz
          exact (lt_irrefl (1 : ℝ)) (by simp [hz_norm] at hz)
      · exact hc.comp (Continuous.continuousOn <| by continuity) fun x hx =>
          by simp [Complex.norm_exp]
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact ContinuousOn.mul continuousOn_const <|
        hc.comp (Continuous.continuousOn <| by continuity) fun x hx =>
          by simp [Complex.norm_exp]
    · intro t ht₁; gcongr
      · convert non_neg_boundary u t h_pos hc using 1
      · exact sub_nonneg_of_le (pow_le_one₀ (norm_nonneg _) (le_of_lt (by simpa using hz)))
      · exact pow_pos (sub_pos.mpr (by simpa using hz)) _
      · exact sub_nonneg.2 (le_of_lt (by simpa using hz))
      · have := norm_sub_norm_le (Complex.exp (t * Complex.I)) z; aesop
  have h_integral : ∫ t in (0 : ℝ)..(2 * π), u (exp (t * Complex.I)) = 2 * π := by
    have h_integral : u 0 = (1 / (2 * π)) * ∫ t in (0 : ℝ)..(2 * π),
      u (exp (t * Complex.I)) := by
      convert poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc h_harmonic hc
        (Metric.mem_ball_self zero_lt_one) using 1
      norm_num [Complex.norm_exp]
    rw [h_f_zero] at h_integral
    rw [div_mul_eq_mul_div, eq_div_iff] at h_integral <;> nlinarith [Real.pi_pos]
  calc u z
    = 1 / (2 * π) * ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) /
      ‖cexp (↑t * I) - z‖ ^ 2 * u (cexp (↑t * I)) := h_poisson
  _ ≤ 1 / (2 * π) * ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 * u (cexp (↑t * I)) := by
      apply mul_le_mul_of_nonneg_left h_max
      have h : 0 < (2 * π) := by nlinarith [Real.pi_pos]
      exact one_div_nonneg.mpr (le_of_lt h)
  _ = 1 / (2 * π) * ((1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 * ∫ (t : ℝ) in 0..2 * π, u (cexp (↑t * I))) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
  _ = 1 / (2 * π) * ((1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 * (2 * π)) := by rw [h_integral]
  _ = (1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 := by field_simp
  _ = (1 + ‖z‖) * (1 - ‖z‖) / (1 - ‖z‖) ^ 2 := by ring_nf
  _ = (1 + ‖z‖) / (1 - ‖z‖) := by
      have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      field_simp

lemma harnack_ineq_cont_normalized_lower
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_f_zero : u 0 = 1)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ≤ u z := by
  have h_integral : u z = (1 / (2 * π)) * ∫ t in (0 : ℝ)..(2 * π),
    (1 - ‖z‖ ^ 2) / ‖(exp (t * I)) - z‖ ^ 2 * u (exp (t * I)) := by
    convert poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc
      h_harmonic hc hz using 1
  have h_mean_value : ∫ t in (0 : ℝ)..(2 * π), (1 - ‖z‖ ^ 2) /
    ‖(exp (t * I)) - z‖ ^ 2 * u (exp (t * I)) ≥ ∫ t in (0 : ℝ)..(2 * π),
      (1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2 * u (exp (t * I)) := by
    refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_
    · positivity
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact ContinuousOn.mul continuousOn_const <| hc.comp (Continuous.continuousOn <|
        by continuity) fun x hx => by simp [Complex.norm_exp]
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.div ?_ ?_ ?_
        · exact continuousOn_const
        · fun_prop
        · rw [mem_ball_zero_iff] at hz
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]
          intro x _ heq
          have h_circle : ‖cexp (↑x * I)‖ = 1 := by simp
          have : ‖z‖ = 1 := by
            calc ‖z‖ = ‖cexp (↑x * I)‖ := by rw [← sub_eq_zero.mp heq]
            _ = 1 := h_circle
          linarith [hz]
      · exact hc.comp (Continuous.continuousOn <| by continuity) fun x hx =>
         by simp [Complex.norm_exp]
    · intro x hx₁; gcongr
      · exact non_neg_boundary u x h_pos hc
      · nlinarith only [show ‖z‖ < 1 from by simpa using hz, show ‖z‖ ≥ 0 from norm_nonneg z]
      · rw [mem_ball_zero_iff] at hz
        apply sq_pos_of_pos
        rw [norm_pos_iff]
        intro heq
        have hz_eq : z = cexp (↑x * I) := by
          rw [sub_eq_zero] at heq
          exact heq.symm
        have hz_norm : ‖z‖ = 1 := by
          simp [hz_eq]
        exact (lt_irrefl (1 : ℝ)) (by simp [hz_norm] at hz)
      · exact le_trans (norm_sub_le _ _) (by simp [Complex.norm_exp]);
  have h_mean_value : ∫ t in (0 : ℝ)..(2 * π), u (exp (t * I)) = 2 * π * u 0 := by
    have := @poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc u 0
    simp at this
    grind
  simp_all only [mem_ball, dist_zero_right, division_def, mul_inv_rev, one_mul,
    intervalIntegral.integral_const_mul, mul_one, ge_iff_le]
  convert mul_le_mul_of_nonneg_left ‹_› (show 0 ≤ π⁻¹ * 2⁻¹ by positivity) using 1
  · rfl
  · field_simp
    ring

/--
Removing the normalization at `0` from Lemma `harnack_ineq_normalized_cont`.
-/
private lemma harnack_ineq_cont
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by
  set v := fun w => u w / u 0 with hv
  have hv_pos : ∀ w ∈ ball (0 : ℂ) 1, 0 < v w := by
    intro w hw
    simp only [hv]
    exact div_pos (h_pos w hw) (h_pos 0 (mem_ball_self zero_lt_one))
  have hv_zero : v 0 = 1 := by
    simp only [hv, div_self_eq_one₀, ne_eq]
    exact ne_of_gt (h_pos 0 (mem_ball_self one_pos))
  have hv_harmonic : HarmonicOnNhd v (ball 0 1) := by
    intro w hw
    change HarmonicAt (fun z => u z / u 0) w
    have : (fun z => u z / u 0) = (1 / u 0) • u := by
      ext; simp [smul_eq_mul]; ring
    rw [this]
    apply (h_harmonic w hw).const_smul
  have hv_cont : ContinuousOn v (closedBall 0 1) := by
    apply ContinuousOn.div hc continuousOn_const
    intro w _
    exact ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one))
  have lower_bound := harnack_ineq_cont_normalized_lower v hv_pos hv_zero hv_harmonic hv_cont z hz
  have upper_bound := harnack_ineq_cont_normalized_upper v hv_pos hv_zero hv_harmonic hv_cont z hz
  simp only [hv] at lower_bound upper_bound
  have h0_ne : u 0 ≠ 0 := ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one))
  have h0_ge : u 0 > 0 := h_pos 0 (mem_ball_self zero_lt_one)
  constructor
  · calc (1 - ‖z‖) / (1 + ‖z‖) * u 0
      _ ≤ (u z / u 0) * u 0 := by apply mul_le_mul_of_nonneg_right lower_bound (le_of_lt h0_ge)
      _ = u z := by exact div_mul_cancel₀ (u z) h0_ne
  · calc u z
      = (u z / u 0) * u 0 := by field_simp [h0_ne]
    _ ≤ ((1 + ‖z‖) / (1 - ‖z‖)) * u 0 := by
      exact mul_le_mul_of_nonneg_right upper_bound (le_of_lt h0_ge)
    _ = u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by ring

/-- The scaled version of a harmonic function. -/
private lemma harmonic_scaling
    (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 1) :
    let v : ℂ → ℝ := fun w => u (r * w)
    HarmonicOnNhd v (ball (0 : ℂ) 1):= by
      intro v
      simp only [Set.mem_Ioo] at hr
      have hfu : ∃ (f : ℂ → ℂ), AnalyticOn ℂ f (ball 0 1) ∧
        EqOn (fun (z : ℂ) => (f z).re) u (ball 0 1) := by
        obtain ⟨f,hf⟩ := hu.exists_analyticOnNhd_ball_re_eq
        use f
        exact ⟨hf.1.analyticOn, hf.2⟩
      obtain ⟨f, hf, hf_eq⟩ := hfu
      have hv_analytic : AnalyticOn ℂ (fun w => f (r * w)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn]
        · apply DifferentiableOn.comp (hf.differentiableOn) ?_
          · intro x hx
            rw [mem_ball_zero_iff] at hx ⊢
            calc ‖↑r * x‖
              = |r| * ‖x‖ := by simp [Complex.norm_real, abs_of_pos hr.1]
            _ = r * ‖x‖ := by rw [abs_of_pos hr.1]
            _ < r * 1 := by apply mul_lt_mul_of_pos_left hx hr.1
            _ = r := by ring
            _ < 1 := hr.2
          · exact (DifferentiableOn.mul (differentiableOn_const _) differentiableOn_id)
        · exact isOpen_ball
      have hv_harmonic : ∀ w ∈ ball 0 1, HarmonicAt (fun w => (f (r * w)).re) w := by
        intro w hw
        have hv_analytic_at_w : AnalyticAt ℂ (fun w => f (r * w)) w := by
          apply_rules [DifferentiableOn.analyticAt, hv_analytic.differentiableOn]
          exact isOpen_ball.mem_nhds hw
        exact AnalyticAt.harmonicAt_re hv_analytic_at_w
      have hv_eq : ∀ w ∈ ball 0 1, v w = (f (r * w)).re := by
        intro w hw
        specialize hf_eq (show (r : ℂ) * w ∈ ball 0 1 from
                          by simpa [abs_of_pos hr.1]
                          using by nlinarith [norm_nonneg w,
                                              show (‖w‖ : ℝ) < 1 from by simpa using hw])
        exact hf_eq.symm
      intro w hw
      have hv_harmonic_at_w : ∀ᶠ w in nhds w, v w = (f (r * w)).re := by
        exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_ball hw) hv_eq
      exact (harmonicAt_congr_nhds hv_harmonic_at_w).mpr (hv_harmonic w hw)

/-- Scaled version of Harnack's inequality for a smaller radius r < 1. -/
private lemma harnack_ineq_aux
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 1)
    (z : ℂ) (hz : ‖z‖ < r) :
    (r - ‖z‖) / (r + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (r + ‖z‖) / (r - ‖z‖) := by
      set v : ℂ → ℝ := fun w => u (r * w)
      have hv_harmonic : HarmonicOnNhd v (ball (0 : ℂ) 1) := harmonic_scaling u h_harmonic r hr
      have hv_ineq : (1 - ‖z / r‖) / (1 + ‖z / r‖) * v 0 ≤ v (z / r) ∧
        v (z / r) ≤ v 0 * (1 + ‖z / r‖) / (1 - ‖z / r‖) := by
        have hv_cont : ContinuousOn v (closedBall 0 1) := by
          refine ContinuousOn.comp (t:= ball 0 1) ?_ ?_ ?_
          · intro z hz
            have := h_harmonic z hz
            exact this.1.continuousAt.continuousWithinAt
          · exact continuousOn_const.mul continuousOn_id
          · exact fun x hx =>
              by simpa [abs_of_pos hr.1] using
                by nlinarith [hr.1, hr.2, show ‖x‖ ≤ 1 from by simpa using hx.out]
        apply harnack_ineq_cont v (fun w hw => by
          apply h_pos
          simpa [abs_of_pos hr.1] using
            by nlinarith [hr.1, hr.2, norm_nonneg w, show ‖w‖ < 1 from by simpa using hw])
          hv_harmonic hv_cont (z / r) (by simp_all [div_lt_iff₀, abs_of_pos hr.1])
      simp only [Set.mem_Ioo] at hr
      convert hv_ineq using 2 <;> norm_num [abs_of_pos hr.1, mul_div_cancel₀, hr.1.ne']
      · have hr_pos : 0 < r := hr.1
        field_simp [hr_pos.ne']
        ring_nf
        simp [v]
      · have : v (z / r) = u (r * (z / r)) := rfl
        simp [this]; congr 1; field_simp [hr.1.ne']
      · have : v (z / r) = u (r * (z / r)) := rfl
        simp [this]; congr 1; field_simp [hr.1.ne']
      · have : v 0 = u 0 := by simp [v, mul_zero]
        rw [this]
        have hr_pos : 0 < r := hr.1
        field_simp [hr_pos.ne']

/-- **Harnack's inequality for positive harmonic functions.**
A positive harmonic function on the unit disc satisfies
two-sided estimates in terms of the distance to the boundary.
-/
theorem harnack_ineq
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by
  refine ⟨?_, ?_⟩
  · have h_ineq : ∀ r ∈ Set.Ioo ‖z‖ 1, (r - ‖z‖) / (r + ‖z‖) * u 0 ≤ u z := by
      exact fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
        by linarith [hr.1, norm_nonneg z], by linarith [hr.2]⟩ z (by simpa using hr.1) |>.1
    have h_limit : Filter.Tendsto (fun r => (r - ‖z‖) / (r + ‖z‖) * u 0) (
      nhdsWithin 1 (Set.Iio 1)) (nhds ((1 - ‖z‖) / (1 + ‖z‖) * u 0)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.mul (
        ContinuousAt.div (continuousAt_id.sub continuousAt_const) (
          continuousAt_id.add continuousAt_const) (by linarith [norm_nonneg z]))
            continuousAt_const)
    exact le_of_tendsto h_limit (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_ineq)
  · have h_aux : ∀ r ∈ Set.Ioo (‖z‖) 1, u z ≤ u 0 * (r + ‖z‖) / (r - ‖z‖) := by
      exact fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
          by linarith [hr.1, norm_nonneg z], hr.2⟩ z (by simpa using hr.1) |>.2
    have h_lim : Filter.Tendsto (fun r : ℝ => u 0 * (r + ‖z‖) / (r - ‖z‖)) (
      nhdsWithin 1 (Set.Iio 1)) (nhds (u 0 * (1 + ‖z‖) / (1 - ‖z‖))) := by
      exact Filter.Tendsto.div (tendsto_const_nhds.mul (
        continuousWithinAt_id.add continuousWithinAt_const)) (
          continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero_of_ne <|
            by linarith [mem_ball_zero_iff.mp hz])
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_aux)

end LeanPool.LeanComplexAnalysis
