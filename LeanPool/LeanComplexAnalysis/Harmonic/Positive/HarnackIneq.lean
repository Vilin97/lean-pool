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

/-- `t ↦ u (exp (t * I))` is continuous on any set when `u` is continuous on the closed disc. -/
private lemma continuousOn_u_exp {u : ℂ → ℝ} (hc : ContinuousOn u (closedBall 0 1)) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => u (Complex.exp (t * Complex.I))) s :=
  hc.comp (Continuous.continuousOn (by continuity)) fun x _ => by simp [Complex.norm_exp]

lemma non_neg_boundary
    (u : ℂ → ℝ) (t : ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (hc : ContinuousOn u (closedBall 0 1)) :
    0 ≤ u (exp (t * I)) := by
  have h_tendsto : Filter.Tendsto (fun r : ℝ => u (r * exp (t * I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (u (exp (t * I)))) := by
    have h_cont : ContinuousOn (fun r : ℝ => u (r * exp (t * I))) (Set.Icc 0 1) := by
      refine hc.comp ?_ ?_
      · fun_prop
      · norm_num [Set.MapsTo, norm_exp]
        exact fun x hx₁ hx₂ => abs_le.mpr ⟨by linarith, by linarith⟩
    simpa using (h_cont 1 (by norm_num)).tendsto.mono_left
      (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds h_tendsto
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one) fun r hr =>
      le_of_lt (h_pos _ (by simpa [abs_of_nonneg hr.1.le, norm_exp] using hr.2)))

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
          rw [norm_eq_zero, mem_ball_zero_iff] at *
          exact absurd (by simp [sub_eq_zero.mp heq |>.symm] : ‖z‖ = 1) (by linarith)
      · exact continuousOn_u_exp hc _
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact ContinuousOn.mul continuousOn_const (continuousOn_u_exp hc _)
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
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  calc u z
    _ = 1 / (2 * π) * ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) /
        ‖cexp (↑t * I) - z‖ ^ 2 * u (cexp (↑t * I)) := h_poisson
    _ ≤ 1 / (2 * π) * ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) /
        (1 - ‖z‖) ^ 2 * u (cexp (↑t * I)) := by
        exact mul_le_mul_of_nonneg_left h_max (by positivity)
    _ = 1 / (2 * π) * ((1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 *
        ∫ (t : ℝ) in 0..2 * π, u (cexp (↑t * I))) := by
        congr 1
        rw [← intervalIntegral.integral_const_mul]
    _ = (1 + ‖z‖) / (1 - ‖z‖) := by
        rw [h_integral]
        field_simp [show (1 - ‖z‖) ≠ (0 : ℝ) by linarith]
        ring

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
      exact ContinuousOn.mul continuousOn_const (continuousOn_u_exp hc _)
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ (continuousOn_u_exp hc _)
      refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const
      · fun_prop
      · rw [mem_ball_zero_iff] at hz
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]
        intro x _ heq
        exact absurd (by simp [← sub_eq_zero.mp heq] : ‖z‖ = 1) (by linarith)
    · intro x hx₁; gcongr
      · exact non_neg_boundary u x h_pos hc
      · nlinarith only [show ‖z‖ < 1 from by simpa using hz, show ‖z‖ ≥ 0 from norm_nonneg z]
      · rw [mem_ball_zero_iff] at hz
        apply sq_pos_of_pos
        rw [norm_pos_iff]
        intro heq
        exact absurd (by simp [sub_eq_zero.mp heq |>.symm] : ‖z‖ = 1) (by linarith)
      · exact le_trans (norm_sub_le _ _) (by simp [Complex.norm_exp]);
  have h_univ_mean : ∫ t in (0 : ℝ)..(2 * π), u (exp (t * I)) = 2 * π * u 0 := by
    have := @poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc u 0
    simp at this
    grind
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [h_integral]
  have key : (1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2 * (2 * π) ≤
      ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) / ‖cexp (↑t * I) - z‖ ^ 2 * u (cexp (↑t * I)) :=
    calc (1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2 * (2 * π)
        = ∫ (t : ℝ) in 0..2 * π, (1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2 * u (cexp (↑t * I)) := by
          rw [intervalIntegral.integral_const_mul, h_univ_mean, h_f_zero]
          ring
      _ ≤ _ := h_mean_value
  linarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 1 / (2 * π)),
            show (1 / (2 * π)) * ((1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2 * (2 * π)) =
                (1 - ‖z‖) / (1 + ‖z‖) by field_simp; ring]

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
  have hv_pos : ∀ w ∈ ball (0 : ℂ) 1, 0 < v w :=
    fun w hw => div_pos (h_pos w hw) (h_pos 0 (mem_ball_self zero_lt_one))
  have hv_zero : v 0 = 1 :=
    div_self (ne_of_gt (h_pos 0 (mem_ball_self one_pos)))
  have hv_harmonic : HarmonicOnNhd v (ball 0 1) := by
    intro w hw
    change HarmonicAt (fun z => u z / u 0) w
    have : (fun z => u z / u 0) = (1 / u 0) • u := by ext
                                                      simp [smul_eq_mul]
                                                      ring
    rw [this]
    exact (h_harmonic w hw).const_smul
  have hv_cont : ContinuousOn v (closedBall 0 1) :=
    hc.div continuousOn_const fun _ _ => ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one))
  have lower_bound := harnack_ineq_cont_normalized_lower v hv_pos hv_zero hv_harmonic hv_cont z hz
  have upper_bound := harnack_ineq_cont_normalized_upper v hv_pos hv_zero hv_harmonic hv_cont z hz
  simp only [hv] at lower_bound upper_bound
  have h0_pos : u 0 > 0 := h_pos 0 (mem_ball_self zero_lt_one)
  rw [le_div_iff₀ h0_pos] at lower_bound
  rw [div_le_iff₀ h0_pos] at upper_bound
  refine ⟨lower_bound, ?_⟩
  linarith [show u 0 * (1 + ‖z‖) / (1 - ‖z‖) = (1 + ‖z‖) / (1 - ‖z‖) * u 0 from by ring]

/-- The scaled version of a harmonic function. -/
private lemma harmonic_scaling
    (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 1) :
    let v : ℂ → ℝ := fun w => u (r * w)
    HarmonicOnNhd v (ball (0 : ℂ) 1):= by
      intro v
      simp only [Set.mem_Ioo] at hr
      obtain ⟨f, hf_nhd, hf_eq⟩ := hu.exists_analyticOnNhd_ball_re_eq
      have hf := hf_nhd.analyticOn
      have hv_analytic : AnalyticOn ℂ (fun w => f (r * w)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn]
        · apply DifferentiableOn.comp (hf.differentiableOn) ?_
          · intro x hx
            rw [mem_ball_zero_iff] at hx ⊢
            simp only [Complex.norm_mul, Complex.norm_real]
            rw [Real.norm_of_nonneg hr.1.le]
            nlinarith [norm_nonneg x]
          · exact (DifferentiableOn.mul (differentiableOn_const _) differentiableOn_id)
        · exact isOpen_ball
      have hv_harmonic : ∀ w ∈ ball 0 1, HarmonicAt (fun w => (f (r * w)).re) w :=
        fun w hw => (hv_analytic.analyticAt (isOpen_ball.mem_nhds hw)).harmonicAt_re
      have hv_eq : ∀ w ∈ ball 0 1, v w = (f (r * w)).re := fun w hw =>
        (hf_eq (show (r : ℂ) * w ∈ ball 0 1 from by
          rw [mem_ball_zero_iff] at hw ⊢
          simp only [Complex.norm_mul, Complex.norm_real]
          rw [Real.norm_of_nonneg hr.1.le]; nlinarith [norm_nonneg w])).symm
      intro w hw
      exact (harmonicAt_congr_nhds (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) hv_eq)).mpr
        (hv_harmonic w hw)

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
        have hv_cont : ContinuousOn v (closedBall 0 1) :=
          ContinuousOn.comp (t := ball 0 1)
            (fun z hz => (h_harmonic z hz).1.continuousAt.continuousWithinAt)
            (continuousOn_const.mul continuousOn_id)
            (fun x hx => by
              simpa [abs_of_pos hr.1] using by
                nlinarith [hr.1, hr.2, show ‖x‖ ≤ 1 from by simpa using hx.out])
        apply harnack_ineq_cont v (fun w hw => by
          apply h_pos
          simpa [abs_of_pos hr.1] using
            by nlinarith [hr.1, hr.2, norm_nonneg w, show ‖w‖ < 1 from by simpa using hw])
          hv_harmonic hv_cont (z / r) (by simp_all [div_lt_iff₀, abs_of_pos hr.1])
      simp only [Set.mem_Ioo] at hr
      have hv0 : v 0 = u 0 := by simp [v]
      have hvz : v (z / r) = u z := by
        simp only [v]
        congr 1
        field_simp [hr.1.ne']
      convert hv_ineq using 2 <;> norm_num [abs_of_pos hr.1, mul_div_cancel₀, hr.1.ne']
      · rw [hv0]
        field_simp [hr.1.ne']
      · exact hvz.symm
      · exact hvz.symm
      · rw [hv0]
        field_simp [hr.1.ne']

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
  · have h_ineq : ∀ r ∈ Set.Ioo ‖z‖ 1, (r - ‖z‖) / (r + ‖z‖) * u 0 ≤ u z :=
      fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
        by linarith [hr.1, norm_nonneg z], by linarith [hr.2]⟩ z (by simpa using hr.1) |>.1
    have h_limit : Filter.Tendsto (fun r => (r - ‖z‖) / (r + ‖z‖) * u 0) (
        nhdsWithin 1 (Set.Iio 1)) (nhds ((1 - ‖z‖) / (1 + ‖z‖) * u 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.mul (
        ContinuousAt.div (continuousAt_id.sub continuousAt_const) (
          continuousAt_id.add continuousAt_const) (by linarith [norm_nonneg z]))
            continuousAt_const)
    exact le_of_tendsto h_limit (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_ineq)
  · have h_aux : ∀ r ∈ Set.Ioo (‖z‖) 1, u z ≤ u 0 * (r + ‖z‖) / (r - ‖z‖) :=
      fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
          by linarith [hr.1, norm_nonneg z], hr.2⟩ z (by simpa using hr.1) |>.2
    have h_lim : Filter.Tendsto (fun r : ℝ => u 0 * (r + ‖z‖) / (r - ‖z‖)) (
        nhdsWithin 1 (Set.Iio 1)) (nhds (u 0 * (1 + ‖z‖) / (1 - ‖z‖))) :=
      Filter.Tendsto.div (tendsto_const_nhds.mul (
        continuousWithinAt_id.add continuousWithinAt_const)) (
          continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero_of_ne <|
            by linarith [mem_ball_zero_iff.mp hz])
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_aux)

end LeanPool.LeanComplexAnalysis
