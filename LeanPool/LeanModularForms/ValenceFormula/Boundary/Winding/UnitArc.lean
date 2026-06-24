/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.UnitArcHelpers
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit

/-!
# Unit Arc Winding Number

Proves `generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2` for points `s`
on the unit circle arc (`‖s‖ = 1`, `|s.re| < 1/2`, `s.im > 0`).

Uses the helper lemmas from `UnitArcHelpers` together with log ratio/diff tendsto
and strict norm monotonicity on the arc.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Re-positivity for the log-div split: the difference at `t₀-δ'` and the negated difference
at `t₀+δ'` both have positive real part. -/
private lemma unitArc_re_pos_at_offsets (s : ℂ) (t₀ δ' : ℝ)
    (_ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (_hδ'_pos : 0 < δ') (hδ'_left : 1 < t₀ - δ') (hδ'_right : t₀ + δ' < 3) :
    0 < (exp (↑(Real.pi * (1 + (t₀ - δ')) / 6) * I) - s).re ∧
    0 < (-(exp (↑(Real.pi * (1 + (t₀ + δ')) / 6) * I) - s)).re := by
  constructor
  · set θ_m := Real.pi * (1 + (t₀ - δ')) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    have hθ_m_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, hδ'_left]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, hδ'_right]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_m_lt]
  · set θ_p := Real.pi * (1 + (t₀ + δ')) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_sub]
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, hδ'_left]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, hδ'_right]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt]

private lemma unitArc_log_ratio_tendsto (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (_ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3) (_h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ => Complex.log ( (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
      (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < δ ∧ δ < 6 := by
    apply inter_mem self_mem_nhdsWithin
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 6))
  have h_log_exp : Tendsto (fun δ : ℝ => Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [show (0 : ℂ) = Complex.log 1 from (by simp only [Complex.log_one])]
    apply (continuousAt_clog (by simp [slitPlane])).tendsto.comp
    rw [show (1 : ℂ) = cexp (↑(-(Real.pi * 0 / 6)) * I) from
      (by simp only [mul_zero, zero_div, neg_zero, ofReal_zero, zero_mul, Complex.exp_zero])]
    exact Tendsto.mono_left (by fun_prop : Continuous _).continuousAt.tendsto nhdsWithin_le_nhds
  have h_agree : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0),
      Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)) =
      Complex.log ( (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    apply h_ev.mono
    intro δ ⟨hδ_pos, hδ_small⟩
    rw [_h_s_arc]; congr 1; exact (unitArc_ratio_eq t₀ δ hδ_pos hδ_small).symm
  exact h_log_exp.congr' h_agree

private lemma unitArc_log_diff_tendsto (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ =>
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ratio := unitArc_log_ratio_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  have h_ev_agree : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0),
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)) =
      Complex.log ((exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    have h_ev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0),
        0 < δ ∧ δ < min (t₀ - 1) (3 - t₀) := by
      apply inter_mem self_mem_nhdsWithin
      exact nhdsWithin_le_nhds
        (Iio_mem_nhds (lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])))
    apply h_ev.mono; intro δ ⟨hδ_pos, hδ_small⟩
    have hδ_lt1 : δ < t₀ - 1 := lt_of_lt_of_le hδ_small (min_le_left _ _)
    have hδ_lt2 : δ < 3 - t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
    obtain ⟨h_re_a, h_re_b⟩ := unitArc_re_pos_at_offsets s t₀ δ ht₀_Ioo h_s_arc hδ_pos
      (by linarith) (by linarith)
    exact (log_div_of_re_pos h_re_a h_re_b).symm
  exact h_ratio.congr' (h_ev_agree.mono fun _ h => h.symm)

private lemma cos_pi_mul_div_six_abs (x : ℝ) :
    Real.cos (Real.pi * x / 6) = Real.cos (Real.pi * |x| / 6) := by
  rcases le_or_gt x 0 with h | h
  · rw [abs_of_nonpos h, show Real.pi * x / 6 = -(Real.pi * (-x) / 6) from by ring, Real.cos_neg]
  · rw [abs_of_pos h]

private lemma normSq_exp_sub (α β : ℝ) :
    Complex.normSq (exp (↑α * I) - exp (↑β * I)) = 2 - 2 * Real.cos (α - β) := by
  rw [Complex.normSq_apply]
  rw [exp_real_angle_I, exp_real_angle_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
    Complex.sub_re, Complex.add_im, Complex.mul_im, mul_one, Complex.sub_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
    sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]

private lemma unitArc_normSq_at_offset (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (h_in_arc : 1 < t₀ + δ) (h_in_arc' : t₀ + δ < 3) :
    Complex.normSq (fdBoundaryH H (t₀ + δ) - s) = 2 - 2 * Real.cos (Real.pi * δ / 6) := by
  rw [fdBoundary_H_eq_arc h_in_arc h_in_arc', h_s_arc]
  rw [normSq_exp_sub]
  congr 1; congr 1; congr 1; ring

private lemma unitArc_norm_lt_of_abs_lt (s : ℂ) (H : ℝ) (t₀ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t₁ t₂ : ℝ) (ht₁_arc : 1 < t₁) (ht₁_arc' : t₁ < 3) (ht₂_arc : 1 < t₂) (ht₂_arc' : t₂ < 3)
    (habs : |t₁ - t₀| < |t₂ - t₀|) :
    ‖fdBoundaryH H t₁ - s‖ < ‖fdBoundaryH H t₂ - s‖ := by
  rw [show t₁ = t₀ + (t₁ - t₀) from by ring, show t₂ = t₀ + (t₂ - t₀) from by ring]
  have hns₁ := unitArc_normSq_at_offset s H t₀ (t₁ - t₀) h_s_arc (by linarith) (by linarith)
  have hns₂ := unitArc_normSq_at_offset s H t₀ (t₂ - t₀) h_s_arc (by linarith) (by linarith)
  have h_abs_bound : |t₂ - t₀| < 2 := by
    rw [abs_lt]; constructor <;> linarith [ht₀_Ioo.1, ht₀_Ioo.2]
  have hφ₁_nn : 0 ≤ Real.pi * |t₁ - t₀| / 6 := by positivity
  have hφ₂_le_pi : Real.pi * |t₂ - t₀| / 6 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hφ_lt : Real.pi * |t₁ - t₀| / 6 < Real.pi * |t₂ - t₀| / 6 := by nlinarith [Real.pi_pos]
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [hns₁, hns₂, cos_pi_mul_div_six_abs (t₁ - t₀), cos_pi_mul_div_six_abs (t₂ - t₀)]
  linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hφ₁_nn hφ₂_le_pi hφ_lt]

/-! ### Helper 1: Arc outside points have norm > ε -/

private lemma unitArc_arc_outside_gt_eps (s : ℂ) (H : ℝ) (t₀ δ' ε : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ'_pos : 0 < δ') (hδ'_left : 1 < t₀ - δ') (hδ'_right : t₀ + δ' < 3)
    (hδ'_eq : ‖fdBoundaryH H (t₀ + δ') - s‖ = ε)
    (t : ℝ) (ht1 : 1 < t) (ht3 : t < 3) (habs : δ' < |t - t₀|) :
    ε < ‖fdBoundaryH H t - s‖ := by
  rw [← hδ'_eq]
  exact unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc (t₀ + δ') t
    (by linarith [ht₀_Ioo.1]) hδ'_right ht1 ht3
    (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact habs)

/-! ### Helper 2: Arc inside points have norm ≤ ε -/

private lemma unitArc_arc_inside_le_eps (s : ℂ) (H : ℝ) (t₀ δ' ε : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ'_pos : 0 < δ') (hδ'_left : 1 < t₀ - δ') (hδ'_right : t₀ + δ' < 3)
    (hδ'_eq : ‖fdBoundaryH H (t₀ + δ') - s‖ = ε)
    (t : ℝ) (ht1 : 1 < t) (ht3 : t < 3) (habs : |t - t₀| ≤ δ') :
    ‖fdBoundaryH H t - s‖ ≤ ε := by
  rcases eq_or_lt_of_le habs with heq | hlt
  · rw [← hδ'_eq]
    rw [show t = t₀ + (t - t₀) from by ring, Complex.norm_def, Complex.norm_def]
    apply le_of_eq; congr 1
    rw [unitArc_normSq_at_offset s H t₀ (t - t₀) h_s_arc (by linarith) (by linarith),
        unitArc_normSq_at_offset s H t₀ δ' h_s_arc (by linarith [ht₀_Ioo.1]) hδ'_right]
    congr 1; congr 1
    rcases le_or_gt (t - t₀) 0 with h | h
    · have h_neg : t - t₀ = -δ' := by rw [abs_of_nonpos h] at heq; linarith
      rw [h_neg, show Real.pi * (-δ') / 6 = -(Real.pi * δ' / 6) from by ring, Real.cos_neg]
    · rw [abs_of_pos h] at heq; rw [heq]
  · rw [← hδ'_eq]
    exact le_of_lt (unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc t (t₀ + δ')
      ht1 ht3 (by linarith [ht₀_Ioo.1]) hδ'_right
      (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact hlt))

/-! ### Helper 3: Norm classification — left of crossing -/

private lemma unitArc_norm_gt_left (s : ℂ) (H : ℝ) (_hH : 1 < H) (t₀ δ' ε : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hs_re : |s.re| < 1 / 2)
    (hδ'_pos : 0 < δ') (hδ'_left : 1 < t₀ - δ') (hδ'_right : t₀ + δ' < 3)
    (hδ'_eq : ‖fdBoundaryH H (t₀ + δ') - s‖ = ε)
    (hε_lt_d : ε < min (min (1 / 2 - s.re) (s.re + 1 / 2)) (H - 1))
    (t : ℝ) (_ht_mem : t ∈ Icc (0 : ℝ) (t₀ - δ')) (ht_lt : t < t₀ - δ') :
    ε < ‖fdBoundaryH H t - s‖ := by
  by_cases h1 : t ≤ 1
  · calc ε < min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) := hε_lt_d
      _ ≤ 1/2 - s.re := le_trans (min_le_left _ _) (min_le_left _ _)
      _ ≤ ‖fdBoundaryH H t - s‖ := unitArc_min_dist_from_seg1 H s hs_re t h1
  · push Not at h1
    exact unitArc_arc_outside_gt_eps s H t₀ δ' ε ht₀_Ioo h_s_arc hδ'_pos hδ'_left hδ'_right
      hδ'_eq t h1 (by linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)

/-! ### Helper 4: Norm classification — right of crossing -/

private lemma unitArc_norm_gt_right (s : ℂ) (H : ℝ) (hH : 1 < H) (t₀ δ' ε : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hs_re : |s.re| < 1 / 2) (hs_norm : ‖s‖ = 1) (hs_im_pos : 0 < s.im)
    (hδ'_pos : 0 < δ') (hδ'_left : 1 < t₀ - δ') (hδ'_right : t₀ + δ' < 3)
    (hδ'_eq : ‖fdBoundaryH H (t₀ + δ') - s‖ = ε)
    (hε_lt_d : ε < min (min (1 / 2 - s.re) (s.re + 1 / 2)) (H - 1))
    (t : ℝ) (ht_gt : t₀ + δ' < t) (ht5 : t ≤ 5) :
    ε < ‖fdBoundaryH H t - s‖ := by
  by_cases h3 : t < 3
  · exact unitArc_arc_outside_gt_eps s H t₀ δ' ε ht₀_Ioo h_s_arc hδ'_pos hδ'_left hδ'_right
      hδ'_eq t (by linarith) h3 (by rw [abs_of_pos (by linarith)]; linarith)
  · push Not at h3
    calc ε < min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) := hε_lt_d
      _ ≤ ‖fdBoundaryH H t - s‖ :=
        unitArc_min_dist_from_non_arc H hH s hs_norm hs_re hs_im_pos t h3 ht5

/-! ### Helper 5: h_near — arc points within δ have norm ≤ ε -/

/-- For `δ(ε) = 12/π · arcsin(ε/2)`, points within δ of the crossing satisfy `‖γ t - s‖ ≤ ε`. -/
private lemma unitArc_h_near (H : ℝ) (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hw : ℝ) (hhw : hw = min (t₀ - 1) (3 - t₀)) (_hhw_pos : 0 < hw)
    (ε : ℝ) (_hε_pos : 0 < ε)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_hw : δ < hw)
    (hδ_eq : ‖fdBoundaryH H (t₀ + δ) - s‖ = ε)
    (t : ℝ) (habs : |t - t₀| ≤ δ) :
    ‖fdBoundaryH H t - s‖ ≤ ε := by
  have hδ_left : 1 < t₀ - δ := by have := lt_of_lt_of_le hδ_lt_hw (hhw ▸ min_le_left _ _); linarith
  have hδ_right : t₀ + δ < 3 := by
    have := lt_of_lt_of_le hδ_lt_hw (hhw ▸ min_le_right _ _); linarith
  have ht1 : 1 < t := by have : -δ ≤ t - t₀ := (abs_le.mp habs).1; linarith
  have ht3 : t < 3 := by have : t - t₀ ≤ δ := (abs_le.mp habs).2; linarith
  exact unitArc_arc_inside_le_eps s H t₀ δ ε ht₀_Ioo h_s_arc hδ_pos hδ_left hδ_right hδ_eq
    t ht1 ht3 habs

/-! ### Main tendsto lemma, wired through `pv_tendsto_of_crossing_limit` -/

/-- Auxiliary: the log-ratio limit E(ε) → -(πI) as ε → 0⁺, where
E(ε) = log(γ(t₀-δ(ε)) - s) - log(-(γ(t₀+δ(ε)) - s)) - πi and δ = 12/π·arcsin(ε/2). -/
private lemma unitArc_limit_aux (H : ℝ) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hw threshold : ℝ) (hthresh_pos : 0 < threshold)
    (hhw_le_t₀_sub_one : hw ≤ t₀ - 1) (hhw_le_three_sub_t₀ : hw ≤ 3 - t₀)
    (δ_fn : ℝ → ℝ) (hδ_fn_def : δ_fn = fun ε => 12 / Real.pi * Real.arcsin (ε / 2))
    (hδ_lt_hw : ∀ ε, 0 < ε → ε < threshold → δ_fn ε < hw)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_fn ε) :
    Tendsto (fun ε => Complex.log (fdBoundaryH H (t₀ - δ_fn ε) - s) -
        Complex.log (-(fdBoundaryH H (t₀ + δ_fn ε) - s)) - ↑Real.pi * I)
      (nhdsWithin 0 (Ioi 0)) (nhds (-(↑Real.pi * I))) := by
  have h_diff := unitArc_log_diff_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  set f_diff := fun δ => Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
    Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))
  have hδ_fn_to_zero : Tendsto δ_fn (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Continuous δ_fn := by
        rw [hδ_fn_def]
        exact continuous_const.mul (Real.continuous_arcsin.comp (continuous_id'.div_const 2))
      have h0 : δ_fn 0 = 0 := by simp [hδ_fn_def, Real.arcsin_zero]
      simpa [h0] using hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ε hε => Set.mem_Ioi.mpr (by
        simp only [hδ_fn_def]
        have hε_pos : 0 < ε := Set.mem_Ioi.mp hε
        exact mul_pos (by positivity) (Real.arcsin_pos.mpr (by linarith)))
  have h_comp : Tendsto (f_diff ∘ δ_fn) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    h_diff.comp hδ_fn_to_zero
  have h_ev : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      Complex.log (fdBoundaryH H (t₀ - δ_fn ε) - s) -
        Complex.log (-(fdBoundaryH H (t₀ + δ_fn ε) - s)) - ↑Real.pi * I =
      (f_diff ∘ δ_fn) ε - ↑Real.pi * I := by
    filter_upwards [Ioo_mem_nhdsGT hthresh_pos] with ε hε
    simp only [f_diff, Function.comp]
    have hδ_lt := hδ_lt_hw ε hε.1 hε.2
    have hδ_pos' := hδ_pos ε hε.1 hε.2
    have hδ_lt_t₀m1 : δ_fn ε < t₀ - 1 := lt_of_lt_of_le hδ_lt hhw_le_t₀_sub_one
    have hδ_lt_3mt₀ : δ_fn ε < 3 - t₀ := lt_of_lt_of_le hδ_lt hhw_le_three_sub_t₀
    have hδ_left : 1 < t₀ - δ_fn ε := by linarith
    have hδ_right : t₀ + δ_fn ε < 3 := by linarith
    rw [fdBoundary_H_eq_arc hδ_left (by linarith [ht₀_Ioo.2, hδ_pos']),
        fdBoundary_H_eq_arc (by linarith [ht₀_Ioo.1, hδ_pos']) hδ_right]
  have h_sub : Tendsto (fun ε => (f_diff ∘ δ_fn) ε - ↑Real.pi * I)
      (nhdsWithin 0 (Ioi 0)) (nhds (0 - ↑Real.pi * I)) :=
    h_comp.sub tendsto_const_nhds
  rw [show (-(↑Real.pi * I) : ℂ) = 0 - ↑Real.pi * I from by ring]
  exact h_sub.congr' (h_ev.mono fun ε h => h.symm)

/-- Auxiliary: the FTC bundle for the arc crossing.
Given a δ-function `δ_fn` with the usual arcsin form and a half-width `hw`, the far-segment
integrals of `(γ - s)⁻¹ · γ'` equal the log difference
`log(γ(t₀-δ) - s) - log(-(γ(t₀+δ) - s)) - πi`. -/
private lemma unitArc_ftc_bundle_aux (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hw threshold : ℝ)
    (hhw_le_t₀_sub_one : hw ≤ t₀ - 1) (hhw_le_three_sub_t₀ : hw ≤ 3 - t₀)
    (δ_fn : ℝ → ℝ)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_fn ε)
    (hδ_lt_hw : ∀ ε, 0 < ε → ε < threshold → δ_fn ε < hw) :
    ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ *
        deriv (fdBoundaryH H) t) volume 0 (t₀ - δ_fn ε) ∧
      IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ *
        deriv (fdBoundaryH H) t) volume (t₀ + δ_fn ε) 5 ∧
      (∫ t in (0 : ℝ)..(t₀ - δ_fn ε),
          (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) +
        (∫ t in (t₀ + δ_fn ε)..5,
          (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) =
      Complex.log (fdBoundaryH H (t₀ - δ_fn ε) - s) -
        Complex.log (-(fdBoundaryH H (t₀ + δ_fn ε) - s)) - ↑Real.pi * I := by
  intro ε hε_pos hε_lt
  have hδ_pos' := hδ_pos ε hε_pos hε_lt
  have hδ_lt := hδ_lt_hw ε hε_pos hε_lt
  have hδ_lt_t₀m1 : δ_fn ε < t₀ - 1 := lt_of_lt_of_le hδ_lt hhw_le_t₀_sub_one
  have hδ_lt_3mt₀ : δ_fn ε < 3 - t₀ := lt_of_lt_of_le hδ_lt hhw_le_three_sub_t₀
  have hδ_left : 1 < t₀ - δ_fn ε := by linarith
  have hδ_right : t₀ + δ_fn ε < 3 := by linarith
  obtain ⟨hint_l, hint_r, h_sum⟩ := unitArc_ftc_value H hH s hs_norm hs_re hs_im_pos
    (δ_fn ε) hδ_pos' t₀ ht₀_Ioo h_s_arc hδ_left hδ_right
  have h_deriv_eq : ∀ t : ℝ,
      deriv (fun u => fdBoundaryH H u - s) t = deriv (fdBoundaryH H) t :=
    fun t => deriv_sub_const (f := fdBoundaryH H) _
  have h_integrand_eq : ∀ t : ℝ,
      deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s) =
      (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t :=
    fun t => by rw [h_deriv_eq, div_eq_mul_inv, mul_comm]
  refine ⟨(intervalIntegrable_congr (fun t _ => h_integrand_eq t)).mp hint_l,
          (intervalIntegrable_congr (fun t _ => h_integrand_eq t)).mp hint_r, ?_⟩
  have h_congr : ∀ a b : ℝ,
      ∫ t in a..b, (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t =
      ∫ t in a..b, deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s) :=
    fun a b => intervalIntegral.integral_congr (fun t _ => (h_integrand_eq t).symm)
  rw [h_congr, h_congr, h_sum]
  obtain ⟨h_re_l, h_re_r⟩ := unitArc_re_pos_at_offsets s t₀ (δ_fn ε) ht₀_Ioo h_s_arc
    hδ_pos' hδ_left hδ_right
  rw [fdBoundary_H_eq_arc hδ_left (by linarith [hδ_lt_3mt₀] : t₀ - δ_fn ε < 3),
      fdBoundary_H_eq_arc (by linarith [ht₀_Ioo.1, hδ_pos'] : 1 < t₀ + δ_fn ε) hδ_right,
      log_div_of_re_pos h_re_l h_re_r]

private lemma unitArc_winding_aux (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (_hg_at_t₀ : fdBoundaryH H t₀ = s) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5, if ‖fdBoundaryH H t - s‖ > ε then
      (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  set d_min := min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) with hd_min_def
  have hd_min_pos : 0 < d_min := unitArc_min_dist_pos s hs_norm hs_re hs_im_pos H hH
  set hw := min (t₀ - 1) (3 - t₀) with hhw_def
  have hhw_pos : 0 < hw := lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])
  have hhw_le_t₀_sub_one : hw ≤ t₀ - 1 := min_le_left _ _
  have hhw_le_three_sub_t₀ : hw ≤ 3 - t₀ := min_le_right _ _
  have hsin_hw : 0 < Real.sin (Real.pi * hw / 12) := by
    apply Real.sin_pos_of_pos_of_lt_pi; · positivity
    · nlinarith [Real.pi_pos]
  set threshold := min d_min (2 * Real.sin (Real.pi * hw / 12)) with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hd_min_pos (by positivity)
  set δ_fn : ℝ → ℝ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2) with hδ_fn_def
  have hδ_lt_hw : ∀ ε, 0 < ε → ε < threshold → δ_fn ε < hw := by
    intro ε hε_pos hε_lt
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi * hw / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi * hw / 12 := by
      have hπhw12 : Real.pi * hw / 12 = Real.arcsin (Real.sin (Real.pi * hw / 12)) :=
        (Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])).symm
      rw [hπhw12]
      apply Real.arcsin_lt_arcsin (by linarith)
      · linarith
      · exact Real.sin_le_one _
    simp only [hδ_fn_def]
    calc 12 / Real.pi * Real.arcsin (ε / 2) < 12 / Real.pi * (Real.pi * hw / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (by positivity)
      _ = hw := by field_simp
  have hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_fn ε := by
    intro ε hε_pos _
    simpa only [hδ_fn_def] using mul_pos (by positivity) (Real.arcsin_pos.mpr (by linarith))
  have hδ_small : ∀ ε, 0 < ε → ε < threshold → δ_fn ε < min (t₀ - 0) (5 - t₀) := by
    intro ε hε_pos hε_lt
    have hδ_lt := hδ_lt_hw ε hε_pos hε_lt
    apply lt_min
    · linarith [ht₀_Ioo.1, hhw_le_t₀_sub_one, hδ_lt]
    · linarith [ht₀_Ioo.2, hhw_le_three_sub_t₀, hδ_lt]
  have hδ_norm_eq : ∀ ε, 0 < ε → ε < threshold →
      ‖fdBoundaryH H (t₀ + δ_fn ε) - s‖ = ε := by
    intro ε hε_pos hε_lt
    have hδ_lt := hδ_lt_hw ε hε_pos hε_lt
    have hδ_lt_t₀m1 : δ_fn ε < t₀ - 1 := lt_of_lt_of_le hδ_lt hhw_le_t₀_sub_one
    have hδ_lt_3mt₀ : δ_fn ε < 3 - t₀ := lt_of_lt_of_le hδ_lt hhw_le_three_sub_t₀
    have hδ_left : 1 < t₀ - δ_fn ε := by linarith
    have hδ_right : t₀ + δ_fn ε < 3 := by linarith
    have hδ_pos' := hδ_pos ε hε_pos hε_lt
    have h_arc_left : 1 < t₀ + δ_fn ε := by linarith [ht₀_Ioo.1, hδ_pos']
    rw [Complex.norm_def,
        unitArc_normSq_at_offset s H t₀ (δ_fn ε) h_s_arc h_arc_left (by linarith [hδ_right])]
    -- 2 - 2·cos(π·δ/6) = 4·sin²(π·δ/12)
    have hangle : δ_fn ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
      simp only [hδ_fn_def]; field_simp
    rw [show Real.pi * δ_fn ε / 6 = 2 * (δ_fn ε * Real.pi / 12) from by ring]
    have h2sin : 2 - 2 * Real.cos (2 * (δ_fn ε * Real.pi / 12)) =
        (2 * Real.sin (δ_fn ε * Real.pi / 12)) ^ 2 := by
      have := Real.sin_sq (δ_fn ε * Real.pi / 12)
      nlinarith [Real.sin_sq (δ_fn ε * Real.pi / 12), Real.cos_sq (δ_fn ε * Real.pi / 12)]
    have hsin_pos : 0 < Real.sin (δ_fn ε * Real.pi / 12) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · have := hδ_lt_hw ε hε_pos hε_lt
        nlinarith [Real.pi_pos]
    have hε_half_bounds : -1 ≤ ε / 2 ∧ ε / 2 ≤ 1 := by
      constructor
      · linarith
      · have hthresh_le : threshold ≤ 2 * Real.sin (Real.pi * hw / 12) :=
          min_le_right _ _
        nlinarith [Real.sin_le_one (Real.pi * hw / 12)]
    rw [h2sin, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith), hangle,
        Real.sin_arcsin hε_half_bounds.1 hε_half_bounds.2]
    ring
  have h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (0 : ℝ) 5, δ_fn ε < |t - t₀| → ε < ‖fdBoundaryH H t - s‖ := by
    intro ε hε_pos hε_lt t ht_mem habs
    have hε_lt_d : ε < d_min := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hδ_lt := hδ_lt_hw ε hε_pos hε_lt
    have hδ_pos' := hδ_pos ε hε_pos hε_lt
    have hδ_lt_t₀m1 : δ_fn ε < t₀ - 1 := lt_of_lt_of_le hδ_lt hhw_le_t₀_sub_one
    have hδ_lt_3mt₀ : δ_fn ε < 3 - t₀ := lt_of_lt_of_le hδ_lt hhw_le_three_sub_t₀
    have hδ_left : 1 < t₀ - δ_fn ε := by linarith
    have hδ_right : t₀ + δ_fn ε < 3 := by linarith
    have hδ_eq := hδ_norm_eq ε hε_pos hε_lt
    rcases lt_or_ge t (t₀ - δ_fn ε) with ht_left | ht_right
    · exact unitArc_norm_gt_left s H hH t₀ (δ_fn ε) ε ht₀_Ioo h_s_arc hs_re
        hδ_pos' hδ_left hδ_right hδ_eq hε_lt_d t ⟨ht_mem.1, le_of_lt ht_left⟩ ht_left
    · have ht_right' : t₀ + δ_fn ε < t := by
        rcases le_or_gt t₀ t with h_t_ge | h_t_lt
        · rw [abs_of_nonneg (by linarith)] at habs; linarith
        · exfalso
          have h_abs_eq : |t - t₀| = t₀ - t := by rw [abs_of_neg (sub_neg.mpr h_t_lt)]; ring
          have habs' : δ_fn ε < t₀ - t := h_abs_eq ▸ habs
          linarith
      exact unitArc_norm_gt_right s H hH t₀ (δ_fn ε) ε ht₀_Ioo h_s_arc hs_re hs_norm hs_im_pos
        hδ_pos' hδ_left hδ_right hδ_eq hε_lt_d t ht_right' ht_mem.2
  have h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ_fn ε → ‖fdBoundaryH H t - s‖ ≤ ε :=
    fun ε hε_pos hε_lt t habs =>
      unitArc_h_near H s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc hw rfl hhw_pos
        ε hε_pos (δ_fn ε) (hδ_pos ε hε_pos hε_lt) (hδ_lt_hw ε hε_pos hε_lt)
        (hδ_norm_eq ε hε_pos hε_lt) t habs
  set E := fun ε => Complex.log (fdBoundaryH H (t₀ - δ_fn ε) - s) -
    Complex.log (-(fdBoundaryH H (t₀ + δ_fn ε) - s)) - ↑Real.pi * I with hE_def
  have h_ftc_bundle := unitArc_ftc_bundle_aux H hH s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo
    h_s_arc hw threshold hhw_le_t₀_sub_one hhw_le_three_sub_t₀ δ_fn hδ_pos hδ_lt_hw
  have h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds (-(↑Real.pi * I))) :=
    unitArc_limit_aux H s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
      hw threshold hthresh_pos hhw_le_t₀_sub_one hhw_le_three_sub_t₀
      δ_fn hδ_fn_def hδ_lt_hw hδ_pos
  exact ContourIntegral.pv_tendsto_of_crossing_limit
    (t₀ := t₀) (ht₀ := ⟨by linarith [ht₀_Ioo.1], by linarith [ht₀_Ioo.2]⟩)
    (threshold := threshold) (hthresh := hthresh_pos)
    (δ := δ_fn) (E := E) hδ_pos hδ_small h_far h_near
    (fun ε hε_pos hε_lt => (h_ftc_bundle ε hε_pos hε_lt).2.2)
    (fun ε hε_pos hε_lt => (h_ftc_bundle ε hε_pos hε_lt).1)
    (fun ε hε_pos hε_lt => (h_ftc_bundle ε hε_pos hε_lt).2.1)
    h_limit

private lemma unitArc_winding_tendsto (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5, if ‖fdBoundaryH H t - s‖ > ε then
      (fdBoundaryH H t - s)⁻¹ * deriv (fun u => fdBoundaryH H u - s) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  have hg_at_t₀ := unitArc_fdBoundary_eq H s hs_norm hs_re hs_im_pos
  have h_s_arc : s = exp (↑(Real.pi * (1 + (6 * Real.arccos s.re / Real.pi - 1)) / 6) * I) := by
    rw [← fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2]; exact hg_at_t₀.symm
  have hd : ∀ t, deriv (fun u => fdBoundaryH H u - s) t = deriv (fdBoundaryH H) t :=
    fun t => deriv_sub_const (f := fdBoundaryH H) _
  simp_rw [hd]
  exact unitArc_winding_aux H hH s hs_norm hs_re hs_im_pos
    (6 * Real.arccos s.re / Real.pi - 1) ht₀_Ioo h_s_arc hg_at_t₀

/-- **Main theorem**: gWN = −1/2 at smooth arc points. -/
theorem gWN_fdBoundary_H_eq_neg_half_of_unitArc (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2 := by
  apply ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
  convert unitArc_winding_tendsto H hH s hs_norm hs_re hs_im_pos using 2
  simp [sub_zero, gt_iff_lt]
