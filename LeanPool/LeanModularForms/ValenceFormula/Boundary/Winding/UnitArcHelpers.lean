/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.RightEdge

/-!
# Unit Arc Winding Number Helpers

Helper lemmas for proving `generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2`
for points `s` on the unit circle arc of the fundamental domain
(`‖s‖ = 1`, `|s.re| < 1/2`, `s.im > 0`).

Contains parameterization, separation, slitPlane conditions, and the FTC value computation.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The crossing parameter `t₀ = 6·arccos(s.re)/π − 1` lies in `(1, 3)`. -/
lemma unitArc_t₀_mem_Ioo (s : ℂ) (hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im) :
    6 * Real.arccos s.re / Real.pi - 1 ∈ Ioo (1 : ℝ) 3 := by
  set θ₀ := Real.arccos s.re with hθ₀_def
  have hs_re_bound : s.re ∈ Ioo (-1/2 : ℝ) (1/2) := by
    have h := abs_lt.mp hs_re; exact ⟨by linarith [h.1], h.2⟩
  have hcos_third : Real.arccos (1/2 : ℝ) = Real.pi / 3 := by
    rw [show (1/2 : ℝ) = Real.cos (Real.pi / 3) from (Real.cos_pi_div_three).symm]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hcos_two_third : Real.arccos (-1/2 : ℝ) = 2 * Real.pi / 3 := by
    rw [show (-1/2 : ℝ) = Real.cos (2 * Real.pi / 3) from by
      rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; ring]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hθ₀_lower : Real.pi / 3 < θ₀ := by
    rw [← hcos_third]
    exact Real.arccos_lt_arccos (by linarith [hs_re_bound.1]) hs_re_bound.2 (by norm_num)
  have hθ₀_upper : θ₀ < 2 * Real.pi / 3 := by
    rw [← hcos_two_third]
    exact Real.arccos_lt_arccos (by norm_num) (by linarith [hs_re_bound.1])
        (by linarith [hs_re_bound.2])
  constructor
  · rw [show (1 : ℝ) < 6 * θ₀ / Real.pi - 1 ↔ 2 * Real.pi < 6 * θ₀ from by
      rw [lt_sub_iff_add_lt, lt_div_iff₀ Real.pi_pos]; ring_nf]
    linarith
  · rw [show 6 * θ₀ / Real.pi - 1 < (3 : ℝ) ↔ 6 * θ₀ < 4 * Real.pi from by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ Real.pi_pos]; ring_nf]
    linarith

/-- `fdBoundaryH H` passes through `s` at the arc parameter `t₀`. -/
lemma unitArc_fdBoundary_eq (H : ℝ) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im) :
    let t₀ := 6 * Real.arccos s.re / Real.pi - 1
    fdBoundaryH H t₀ = s := by
  intro t₀
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2]
  have h_angle : Real.pi * (1 + t₀) / 6 = Real.arccos s.re := by
    simp only [t₀]; field_simp; ring
  rw [h_angle]
  rw [exp_real_angle_I]
  have hs_re_range : s.re ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have := abs_le.mp (le_of_lt hs_re |>.trans (by norm_num : (1 : ℝ)/2 ≤ 1))
      linarith [(abs_le.mp (le_of_lt hs_re)).1]
    · linarith [(abs_lt.mp hs_re).2]
  rw [Real.cos_arccos hs_re_range.1 hs_re_range.2]
  have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
    have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
    simp only [Complex.normSq_apply] at h2; nlinarith
  have h_sin : Real.sin (Real.arccos s.re) = s.im := by
    rw [Real.sin_arccos]
    have h1m : 1 - s.re ^ 2 = s.im ^ 2 := by linarith
    rw [h1m, Real.sqrt_sq (le_of_lt hs_im_pos)]
  rw [h_sin]
  exact Complex.re_add_im s

private lemma unitArc_unique_crossing (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im) :
    let t₀ := 6 * Real.arccos s.re / Real.pi - 1
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundaryH H t = s → t = t₀ := by
  intro t₀ t ht hs_eq
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
    linarith
  by_cases h1 : t ≤ 1
  · simp only [fdBoundaryH, h1, ↓reduceIte] at hs_eq
    have hre := congr_arg Complex.re hs_eq
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im] at hre
    have := (abs_lt.mp hs_re).2
    linarith
  · push Not at h1
    by_cases h3 : t ≤ 3
    · by_cases h1' : t = 1
      · subst h1'
        simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_refl _, ↓reduceIte] at hs_eq
        have hre := congr_arg Complex.re hs_eq
        simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one,
          zero_sub] at hre
        have := (abs_lt.mp hs_re).2
        linarith
      · have ht1 : 1 < t := lt_of_le_of_ne (le_of_lt h1) (Ne.symm h1')
        have ht3 : t < 3 := lt_of_le_of_ne h3 (by
          intro h3_eq; subst h3_eq
          simp only [fdBoundaryH, show ¬((3 : ℝ) ≤ 1) from by norm_num, ↓reduceIte,
            show ¬((3 : ℝ) ≤ 2) from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _] at hs_eq
          have hre := congr_arg Complex.re hs_eq
          have h_angle : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
              ↑(2 * Real.pi / 3) := by push_cast; ring
          rw [h_angle] at hre
          rw [exp_real_angle_I, cos_two_pi_div_three] at hre
          simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero] at hre
          have := (abs_lt.mp hs_re).1; linarith)
        rw [fdBoundary_H_eq_arc ht1 ht3] at hs_eq
        have h_s_eq : fdBoundaryH H t₀ = s := unitArc_fdBoundary_eq H s hs_norm hs_re hs_im_pos
        rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2] at h_s_eq
        rw [← h_s_eq] at hs_eq
        have hre := congr_arg Complex.re hs_eq
        simp only [exp_real_angle_I, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
                   mul_zero, zero_mul, sub_self, add_zero] at hre
        set θ := Real.pi * (1 + t) / 6
        set θ₀' := Real.pi * (1 + t₀) / 6
        have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · positivity
          · simp only [θ]; nlinarith [Real.pi_pos, h3]
        have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · simp only [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
          · simp only [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
        have hθ_eq : θ = θ₀' :=
          Real.strictAntiOn_cos.injOn hθ_range hθ₀_range hre
        simp only [θ, θ₀'] at hθ_eq
        nlinarith [Real.pi_pos]
    · push Not at h3
      by_cases h4 : t ≤ 4
      · rw [fdBoundary_H_eq_seg4_H h3 h4] at hs_eq
        have hre := congr_arg Complex.re hs_eq
        simp [fdBoundarySeg4H, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
        have := (abs_lt.mp hs_re).1; linarith
      · push Not at h4
        rw [fdBoundary_H_eq_seg5_H h4] at hs_eq
        have him := congr_arg Complex.im hs_eq
        simp [fdBoundarySeg5H, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
        have hs_im_le : s.im ≤ 1 := by
          have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
            have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
            rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
            simp only [Complex.normSq_apply] at h2; nlinarith
          nlinarith [sq_nonneg s.re]
        linarith
private lemma unitArc_dist_from_seg1 (s : ℂ) (hs_re : |s.re| < 1 / 2) (z : ℂ)
    (hz_re : z.re = 1 / 2) : 1/2 - s.re ≤ ‖z - s‖ := by
  have hd : (z - s).re = 1/2 - s.re := by simp [Complex.sub_re, hz_re]
  calc 1/2 - s.re = |(z - s).re| := by
        rw [hd, abs_of_pos (by linarith [(abs_lt.mp hs_re).2])]
    _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _

private lemma unitArc_dist_from_seg4 (s : ℂ) (hs_re : |s.re| < 1 / 2) (z : ℂ)
    (hz_re : z.re = -1 / 2) : s.re + 1/2 ≤ ‖z - s‖ := by
  have hd : (z - s).re = -1/2 - s.re := by simp [Complex.sub_re, hz_re]
  calc s.re + 1/2 = |(-1/2 - s.re)| := by
        rw [abs_of_nonpos (by linarith [(abs_lt.mp hs_re).1])]; ring
    _ = |(z - s).re| := by rw [hd]
    _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _

private lemma unitArc_dist_from_seg5 (s : ℂ) (hs_norm : ‖s‖ = 1) (H : ℝ) (hH : 1 < H)
    (z : ℂ) (hz_im : z.im = H) : H - 1 ≤ ‖z - s‖ := by
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
      simp only [Complex.normSq_apply] at h2; nlinarith
    nlinarith [sq_nonneg s.re]
  have hd : (z - s).im = H - s.im := by simp [Complex.sub_im, hz_im]
  calc H - 1 ≤ H - s.im := by linarith
    _ = |(z - s).im| := by rw [hd, abs_of_pos (by linarith)]
    _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _

/-- Minimum separation distance for arc points. -/
lemma unitArc_min_dist_pos (s : ℂ) (_hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2)
    (_hs_im_pos : 0 < s.im) (H : ℝ) (hH : 1 < H) :
    0 < min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) := by
  simp only [lt_min_iff]
  exact ⟨⟨by linarith [(abs_lt.mp hs_re).2], by linarith [(abs_lt.mp hs_re).1]⟩,
         by linarith⟩

/-- Non-arc segments of fdBoundaryH stay at distance ≥ d from arc point s. -/
lemma unitArc_min_dist_from_non_arc (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im)
    (t : ℝ) (ht_arc_right : 3 ≤ t) (ht5 : t ≤ 5) :
    min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) ≤ ‖fdBoundaryH H t - s‖ := by
  set d := min (min (1/2 - s.re) (s.re + 1/2)) (H - 1)
  rcases eq_or_lt_of_le ht_arc_right with h3_eq | h3_lt
  · subst h3_eq
    unfold fdBoundaryH
    rw [if_neg (show ¬((3 : ℝ) ≤ 1) from by norm_num),
        if_neg (show ¬((3 : ℝ) ≤ 2) from by norm_num),
        if_pos (show (3 : ℝ) ≤ 3 from le_refl _)]
    have hre : (exp ((↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)).re =
        -1/2 := by
      rw [show (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) * I =
        ↑(2 * Real.pi / 3) * I from by push_cast; ring]
      rw [exp_real_angle_I, cos_two_pi_div_three]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]; norm_num
    calc d ≤ s.re + 1/2 := le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ _ := unitArc_dist_from_seg4 s hs_re _ hre
  · by_cases h4 : t ≤ 4
    · have hre := re_fdBoundary_H_seg4 H t (by linarith) (by linarith) h3_lt h4
      calc d ≤ s.re + 1/2 := le_trans (min_le_left _ _) (min_le_right _ _)
        _ ≤ _ := unitArc_dist_from_seg4 s hs_re _ hre
    · push Not at h4
      have him := im_fdBoundary_H_seg5 H t (by linarith) (by linarith) h3_lt h4
      calc d ≤ H - 1 := min_le_right _ _
        _ ≤ _ := unitArc_dist_from_seg5 s hs_norm H hH _ him

/-- Non-arc segments to the LEFT (t ≤ 1) stay at distance ≥ d from arc point s. -/
lemma unitArc_min_dist_from_seg1 (H : ℝ) (s : ℂ) (hs_re : |s.re| < 1 / 2) (t : ℝ) (ht : t ≤ 1) :
    1/2 - s.re ≤ ‖fdBoundaryH H t - s‖ := by
  rw [fdBoundary_H_eq_seg1_H ht]
  have hre : (fdBoundarySeg1H H t).re = 1/2 := by
    simp [fdBoundarySeg1H, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  exact unitArc_dist_from_seg1 s hs_re _ hre
private lemma unitArc_g_slitPlane_before (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t : ℝ) (ht1 : 1 ≤ t) (htt₀ : t < t₀) :
    (exp (↑(Real.pi * (1 + t) / 6) * I) - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  set θ₀' := Real.pi * (1 + t₀) / 6 with hθ₀_def
  rw [h_s_arc, exp_real_angle_I, exp_real_angle_I, show
    (↑(Real.cos θ) + ↑(Real.sin θ) * I) - (↑(Real.cos θ₀') + ↑(Real.sin θ₀') * I) =
    ↑(Real.cos θ - Real.cos θ₀') + ↑(Real.sin θ - Real.sin θ₀') * I
    from by push_cast; ring]
  have hθ_lt : θ < θ₀' := by simp [hθ_def, hθ₀_def]; nlinarith [Real.pi_pos]
  have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> simp [hθ_def] <;> nlinarith [Real.pi_pos, ht₀_Ioo.2]
  have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> simp [hθ₀_def] <;> nlinarith [Real.pi_pos, ht₀_Ioo.2]
  have h_cos_lt : Real.cos θ > Real.cos θ₀' :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ_range.1 hθ₀_range.2 hθ_lt
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith [h_cos_lt, sq_nonneg (Real.sin θ₀' - Real.sin θ)]

private lemma unitArc_neg_g_slitPlane_after (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1 / 2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t : ℝ) (htt₀ : t₀ < t) (ht3 : t ≤ 3) :
    -(exp (↑(Real.pi * (1 + t) / 6) * I) - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  set θ₀' := Real.pi * (1 + t₀) / 6 with hθ₀_def
  rw [h_s_arc, exp_real_angle_I, exp_real_angle_I,
    show -((↑(Real.cos θ) + ↑(Real.sin θ) * I) - (↑(Real.cos θ₀') + ↑(Real.sin θ₀') * I)) =
    ↑(Real.cos θ₀' - Real.cos θ) +
    ↑(Real.sin θ₀' - Real.sin θ) * I
    from by push_cast; ring]
  have hθ_gt : θ₀' < θ := by simp [hθ_def, hθ₀_def]; nlinarith [Real.pi_pos]
  have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · simp [hθ_def]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    · simp [hθ_def]; have : 1 + t ≤ 4 := by linarith [ht3]
      nlinarith [Real.pi_pos]
  have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · simp [hθ₀_def]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    · simp [hθ₀_def]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
  have h_cos_lt : Real.cos θ₀' > Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_range.1 hθ_range.2 hθ_gt
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith [h_cos_lt, sq_nonneg (Real.sin θ₀' - Real.sin θ)]

private lemma unitArc_neg_g_slitPlane_seg4 (s : ℂ)
    (hs_re : |s.re| < 1 / 2) (H : ℝ) (t : ℝ) (_ht3 : 3 ≤ t) (_ht4 : t ≤ 4) :
    -(fdBoundarySeg4H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [fdBoundarySeg4H, neg_sub]
  change 0 < (s - (-1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)).re
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re]
  linarith [(abs_lt.mp hs_re).1]

private lemma unitArc_neg_g_slitPlane_seg5 (s : ℂ)
    (hs_norm : ‖s‖ = 1) (H : ℝ) (hH : 1 < H) (t : ℝ) :
    -(fdBoundarySeg5H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  simp only [fdBoundarySeg5H, neg_sub]
  simp only [sub_im, add_im, ofReal_im, div_ofNat_im, im_ofNat, zero_div, sub_self, mul_im,
    ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add, ne_eq]
  intro h
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def] at h2
      have hn : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
      rw [Real.sq_sqrt hn] at h2
      simp only [Complex.normSq_apply] at h2
      convert h2 using 1
      ring
    nlinarith [sq_nonneg s.re]
  linarith
/-- The ratio `g(t₀-δ) / (−g(t₀+δ)) = exp(−i·πδ/6)` on the arc. -/
lemma unitArc_ratio_eq (t₀ δ : ℝ) (hδ_pos : 0 < δ) (hδ_small : δ < 6) :
    let g_minus :=
      exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - exp (↑(Real.pi * (1 + t₀) / 6) * I)
    let neg_g_plus :=
      -(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - exp (↑(Real.pi * (1 + t₀) / 6) * I))
    g_minus / neg_g_plus = exp (↑(-(Real.pi * δ / 6)) * I) := by
  dsimp only
  set θ₀ := Real.pi * (1 + t₀) / 6
  set φ := Real.pi * δ / 6 with hφ_def
  have hφ_pos : 0 < φ := by positivity
  have hφ_lt_pi : φ < Real.pi := by simp [hφ_def]; nlinarith [Real.pi_pos]
  rw [show Real.pi * (1 + (t₀ - δ)) / 6 = θ₀ - φ from by simp [θ₀, hφ_def]; ring,
      show Real.pi * (1 + (t₀ + δ)) / 6 = θ₀ + φ from by simp [θ₀, hφ_def]; ring]
  rw [show (↑(θ₀ - φ) * I : ℂ) = ↑θ₀ * I - ↑φ * I from by push_cast; ring,
      show (↑(θ₀ + φ) * I : ℂ) = ↑θ₀ * I + ↑φ * I from by push_cast; ring]
  set z := exp (↑θ₀ * I)
  set w := exp (↑φ * I)
  have h_sub : exp (↑θ₀ * I - ↑φ * I) = z * w⁻¹ := by rw [Complex.exp_sub]; rfl
  have h_add : exp (↑θ₀ * I + ↑φ * I) = z * w := Complex.exp_add _ _
  rw [h_sub, h_add]
  have hz_ne : z ≠ 0 := exp_ne_zero _
  have hw_ne_one : w ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    rw [show w = cexp (↑φ * I) from rfl, exp_ofReal_mul_I_im, one_im] at him
    linarith [Real.sin_pos_of_pos_of_lt_pi hφ_pos hφ_lt_pi]
  rw [show z * w⁻¹ - z = z * (w⁻¹ - 1) from by ring,
      show -(z * w - z) = z * (1 - w) from by ring,
      mul_div_mul_left _ _ hz_ne]
  have hw_ne : w ≠ 0 := exp_ne_zero _
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne_one)
  have h_ratio : (w⁻¹ - 1) / (1 - w) = w⁻¹ := by field_simp [h1w]
  rw [h_ratio]
  simp only [w]
  rw [show (↑(-φ) * I : ℂ) = -(↑φ * I) from by push_cast; ring, Complex.exp_neg]
private lemma unitArc_far_endpoint_correction (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im) :
    Complex.log (-(fdBoundaryH H 0 - s)) =
    Complex.log (fdBoundaryH H 0 - s) - ↑Real.pi * I := by
  set g₀ := fdBoundaryH H 0 - s
  have hg₀_re : g₀.re = 1/2 - s.re := by
    simp [g₀, fdBoundaryH, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def] at h2
      have hn : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
      rw [Real.sq_sqrt hn] at h2
      simp only [Complex.normSq_apply] at h2
      convert h2 using 1
      ring
    nlinarith [sq_nonneg s.re]
  have hg₀_im : g₀.im = H - s.im := by
    simp [g₀, fdBoundaryH, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hg₀_im_pos : 0 < g₀.im := by rw [hg₀_im]; linarith
  have hg₀_ne : g₀ ≠ 0 := by
    intro h; have := congr_arg Complex.im h
    simp only [Complex.zero_im] at this; linarith [hg₀_im_pos]
  simp only [Complex.log]
  rw [norm_neg, arg_neg_eq_arg_sub_pi_iff.mpr (Or.inl hg₀_im_pos)]
  push_cast; ring
private lemma unitArc_g_slitPlane_seg1 (s : ℂ)
    (hs_re : |s.re| < 1 / 2) (H : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryH H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rw [fdBoundary_H_eq_seg1_H ht.2]
  simp [fdBoundarySeg1H, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linarith [(abs_lt.mp hs_re).2]
private lemma unitArc_log_final (s : ℂ) (t₀ δ : ℝ)
    (_ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ_left : 1 < t₀ - δ) (hδ_right : t₀ + δ < 3) (hδ_pos : 0 < δ) :
    let h_arc := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
    0 < (h_arc (t₀ - δ)).re ∧ 0 < (-(h_arc (t₀ + δ))).re := by
  intro h_arc
  constructor
  · change 0 < (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s).re
    set θ_m := Real.pi * (1 + (t₀ - δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.sub_re]
    have hθ_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, _ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, _ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_lt]
  · change 0 < (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)).re
    set θ_p := Real.pi * (1 + (t₀ + δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_sub]
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, _ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, _ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt]

/-- For any `δ > 0` with `t₀-δ > 1` and `t₀+δ < 3`, the δ-split integral
equals `log(g(t₀-δ)/(-g(t₀+δ))) - πI`. -/
private lemma unitArc_deriv_eq_on_Ioo {g h : ℝ → ℂ} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hgh : ∀ s ∈ Ioo a b, g s = h s) : deriv g t = deriv h t :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) hgh)

/-- On `uIoc lo hi` (`lo ≤ hi`), the logderiv quotient of `h` matches that of `g`, a.e.: the two
endpoints form a null set, and on the open interior `g = h` and `deriv g = deriv h`. -/
private lemma unitArc_logDeriv_ae_eq {lo hi : ℝ} (hlo_hi : lo ≤ hi) (g h : ℝ → ℂ)
    (hg_eq : ∀ t, lo < t → t < hi → g t = h t)
    (hderiv_eq : ∀ t ∈ Ioo lo hi, deriv g t = deriv h t) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc lo hi → deriv h t / h t = deriv g t / g t := by
  have h_excl : ({lo, hi} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by
      rw [compl_compl]
      exact (Set.toFinite ({lo, hi} : Set ℝ)).measure_zero volume)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [Set.uIoc_of_le hlo_hi] at ht_mem
  have ht_lo : lo < t := lt_of_le_of_ne ht_mem.1.le
    (fun h => ht_ne (by simp only [mem_insert_iff, mem_singleton_iff]; exact Or.inl h.symm))
  have ht_hi : t < hi := lt_of_le_of_ne ht_mem.2
    (fun h => ht_ne (by simp only [mem_insert_iff, mem_singleton_iff]; exact Or.inr h))
  rw [hg_eq t ht_lo ht_hi, hderiv_eq t ⟨ht_lo, ht_hi⟩]

private lemma unitArc_seg1_eq_arc_at_one (H : ℝ) (s : ℂ) :
    fdBoundarySeg1H H 1 - s = exp (↑(Real.pi * (1 + (1 : ℝ)) / 6) * I) - s := by
  simp only [fdBoundarySeg1H]
  rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
      exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma unitArc_arc_eq_seg4_at_three (H : ℝ) (s : ℂ) :
    exp (↑(Real.pi * (1 + (3 : ℝ)) / 6) * I) - s = fdBoundarySeg4H H 3 - s := by
  simp only [fdBoundarySeg4H]
  rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
      exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
  push_cast; ring

lemma unitArc_ftc_value (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1 / 2) (hs_im_pos : 0 < s.im)
    (δ : ℝ) (hδ_pos : 0 < δ) (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1 : ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ_left : 1 < t₀ - δ) (hδ_right : t₀ + δ < 3) :
    IntervalIntegrable (fun t => deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s))
      volume 0 (t₀ - δ) ∧
    IntervalIntegrable (fun t => deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s))
      volume (t₀ + δ) 5 ∧
    ((∫ t in (0 : ℝ)..(t₀ - δ),
      deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s)) +
    (∫ t in (t₀ + δ)..5, deriv (fun u => fdBoundaryH H u - s) t / (fdBoundaryH H t - s)) =
    Complex.log ((fdBoundaryH H (t₀ - δ) - s) / (-(fdBoundaryH H (t₀ + δ) - s))) -
    ↑Real.pi * I) := by
  set g : ℝ → ℂ := fun t => fdBoundaryH H t - s with hg_def
  set h₀ : ℝ → ℂ := fun t => fdBoundarySeg1H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundarySeg4H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundarySeg5H H t - s
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp only [sub_zero])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp only [sub_zero])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp only [sub_zero])
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [hg_def, h₃]
    rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [hg_def, h₅]
    rw [fdBoundary_H_eq_seg5_H ht4]
  have hep_01 : h₅ 5 = h₀ 0 := by
    simp only [h₀, h₅, fdBoundarySeg1H, fdBoundarySeg5H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := unitArc_seg1_eq_arc_at_one H s
  have hep_3 : h_arc 3 = h₃ 3 := unitArc_arc_eq_seg4_at_three H s
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundarySeg4H, fdBoundarySeg5H]; push_cast; ring
  have hderiv_01 : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = deriv h₀ t := fun t ht =>
    unitArc_deriv_eq_on_Ioo ht (fun s hs => hg_h₀ s (le_of_lt hs.2))
  have hderiv_arc : ∀ t ∈ Ioo (1 : ℝ) 3, deriv g t = deriv h_arc t := fun t ht =>
    unitArc_deriv_eq_on_Ioo ht (fun s hs => hg_arc s hs.1 hs.2)
  have hderiv_3 : ∀ t ∈ Ioo (3 : ℝ) 4, deriv g t = deriv h₃ t := fun t ht =>
    unitArc_deriv_eq_on_Ioo ht (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2))
  have hderiv_5 : ∀ t ∈ Ioo (4 : ℝ) 5, deriv g t = deriv h₅ t := fun t ht =>
    unitArc_deriv_eq_on_Ioo ht (fun s hs => hg_h₅ s hs.1)
  have hslit_seg1 : ∀ t ∈ Icc (0 : ℝ) 1, h₀ t ∈ Complex.slitPlane := by
    intro t ht
    have : (fdBoundaryH H t - s) ∈ Complex.slitPlane :=
      unitArc_g_slitPlane_seg1 s hs_re H t ht
    rwa [← hg_h₀ t ht.2]
  have hslit_arc_before : ∀ t ∈ Icc (1 : ℝ) (t₀ - δ), h_arc t ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht_td⟩
    have htt₀ : t < t₀ := by linarith
    rcases eq_or_lt_of_le ht1 with h_eq | h_lt
    · rw [← h_eq]; rw [← hep_1]; exact hslit_seg1 1 ⟨by norm_num, le_refl _⟩
    · exact unitArc_g_slitPlane_before s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc t
        (le_of_lt h_lt) htt₀
  have hslit_arc_after : ∀ t ∈ Icc (t₀ + δ) (3 : ℝ), -(h_arc t) ∈ Complex.slitPlane := by
    intro t ⟨ht_td, ht3⟩
    have htt₀ : t₀ < t := by linarith
    rcases eq_or_lt_of_le ht3 with h_eq | h_lt
    · rw [h_eq, hep_3]
      exact unitArc_neg_g_slitPlane_seg4 s hs_re H 3 le_rfl (by norm_num)
    · exact unitArc_neg_g_slitPlane_after s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc t
        htt₀ (le_of_lt h_lt)
  have hslit_seg4 : ∀ t ∈ Icc (3 : ℝ) 4, -(h₃ t) ∈ Complex.slitPlane := by
    intro t ht; exact unitArc_neg_g_slitPlane_seg4 s hs_re H t ht.1 ht.2
  have hslit_seg5 : ∀ t ∈ Icc (4 : ℝ) 5, -(h₅ t) ∈ Complex.slitPlane := by
    intro t ⟨ht4, ht5⟩
    have : -(fdBoundarySeg5H H t - s) ∈ Complex.slitPlane :=
      unitArc_neg_g_slitPlane_seg5 s hs_norm H hH t
    simpa [h₅]
  have piece₀ := ftc_log (by norm_num : (0 : ℝ) ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
          funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    hslit_seg1
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₁ := ftc_log (by linarith : (1 : ℝ) ≤ t₀ - δ)
    h_arc_cont.continuousOn (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc_before
  have piece₂ := ftc_log_neg (by linarith : t₀ + δ ≤ 3)
    h_arc_cont.continuousOn (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc_after
  have piece₃ := ftc_log_neg (by norm_num : (3 : ℝ) ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
          funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    hslit_seg4
  have piece₄ := ftc_log_neg (by norm_num : (4 : ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit_seg5
  have h_ae_01 := unitArc_logDeriv_ae_eq (by norm_num : (0 : ℝ) ≤ 1) g h₀
    (fun t _ ht1 => hg_h₀ t (le_of_lt ht1)) hderiv_01
  have h_ae_1_td := unitArc_logDeriv_ae_eq (by linarith : (1 : ℝ) ≤ t₀ - δ) g h_arc
    (fun t ht1 ht2 => hg_arc t ht1 (by linarith))
    (fun t ht => hderiv_arc t ⟨ht.1, by linarith [ht.2]⟩)
  have h_ae_arc_after := unitArc_logDeriv_ae_eq (by linarith : t₀ + δ ≤ 3) g h_arc
    (fun t ht1 ht3 => hg_arc t (by linarith) ht3)
    (fun t ht => hderiv_arc t ⟨by linarith [ht.1], ht.2⟩)
  have h_ae_34 := unitArc_logDeriv_ae_eq (by norm_num : (3 : ℝ) ≤ 4) g h₃
    (fun t ht3 ht4 => hg_h₃ t ht3 (le_of_lt ht4)) hderiv_3
  have h_ae_45 := unitArc_logDeriv_ae_eq (by norm_num : (4 : ℝ) ≤ 5) g h₅
    (fun t ht4 _ => hg_h₅ t ht4) hderiv_5
  have hint_01 : IntervalIntegrable (fun t => deriv g t / g t) volume 0 1 :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_01.mono (fun t ht hm => ht hm)))
  have hint_1_td : IntervalIntegrable (fun t => deriv g t / g t) volume 1 (t₀ - δ) :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_1_td.mono (fun t ht hm => ht hm)))
  have hint_td_3 : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 3 :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc_after.mono (fun t ht hm => ht hm)))
  have hint_34 : IntervalIntegrable (fun t => deriv g t / g t) volume 3 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_34.mono (fun t ht hm => ht hm)))
  have hint_45 : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_45.mono (fun t ht hm => ht hm)))
  refine ⟨hint_01.trans hint_1_td, (hint_td_3.trans hint_34).trans hint_45, ?_⟩
  have hderiv_eq : (fun u => fdBoundaryH H u - s) = g := rfl
  have h_ftc_01 : ∫ t in (0 : ℝ)..1, deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae (h_ae_01.mono (fun t ht hm => ht hm))]
  have h_ftc_1_td : ∫ t in (1 : ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h_arc (t₀ - δ)) - Complex.log (h_arc 1) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae (h_ae_1_td.mono (fun t ht hm => ht hm))]
  have h_ftc_td_3 : ∫ t in (t₀ + δ)..(3 : ℝ), deriv g t / g t =
      Complex.log (-(h_arc 3)) - Complex.log (-(h_arc (t₀ + δ))) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae (h_ae_arc_after.mono (fun t ht hm => ht hm))]
  have h_ftc_34 : ∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t =
      Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae (h_ae_34.mono (fun t ht hm => ht hm))]
  have h_ftc_45 : ∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t =
      Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae (h_ae_45.mono (fun t ht hm => ht hm))]
  have h_split_left : ∫ t in (0 : ℝ)..(t₀ - δ), deriv g t / g t =
      (∫ t in (0 : ℝ)..1, deriv g t / g t) + (∫ t in (1 : ℝ)..(t₀ - δ), deriv g t / g t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_01 hint_1_td]
  have h_split_right : ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t =
      (∫ t in (t₀ + δ)..(3 : ℝ), deriv g t / g t) + (∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t) +
      (∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t) := by
    have h1 : (∫ t in (t₀ + δ)..(3 : ℝ), deriv g t / g t)
        + (∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t) =
        ∫ t in (t₀ + δ)..(4 : ℝ), deriv g t / g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_td_3 hint_34]
    have h2 : (∫ t in (t₀ + δ)..(4 : ℝ), deriv g t / g t)
        + (∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t) =
        ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint_td_3.trans hint_34) hint_45]
    rw [← h2, ← h1]
  simp_rw [show ∀ t, fdBoundaryH H t - s = g t from fun _ => rfl]
  rw [h_split_left, h_ftc_01, h_ftc_1_td,
      h_split_right, h_ftc_td_3, h_ftc_34, h_ftc_45]
  have h_telescope :
    Complex.log (h₀ 1) - Complex.log (h₀ 0) +
    (Complex.log (h_arc (t₀ - δ)) - Complex.log (h_arc 1)) +
    ((Complex.log (-(h_arc 3)) - Complex.log (-(h_arc (t₀ + δ)))) +
     (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
     (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)))) =
    Complex.log (h_arc (t₀ - δ)) - Complex.log (h₀ 0) +
    (Complex.log (-(h₀ 0)) - Complex.log (-(h_arc (t₀ + δ)))) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  rw [h_telescope]
  have h_h₀_is_g₀ : h₀ 0 = fdBoundaryH H 0 - s := by
    simp only [sub_left_inj, h₀]; rw [← fdBoundary_H_eq_seg1_H (by norm_num : (0 : ℝ) ≤ 1)]
  have h_far_corr : Complex.log (-(h₀ 0)) = Complex.log (h₀ 0) - ↑Real.pi * I := by
    rw [h_h₀_is_g₀]
    exact unitArc_far_endpoint_correction H hH s hs_norm hs_re hs_im_pos
  rw [h_far_corr]
  have h_td_arc : g (t₀ - δ) = h_arc (t₀ - δ) := by
    simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc (by linarith) (by linarith)]
  have h_pd_arc : g (t₀ + δ) = h_arc (t₀ + δ) := by
    simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc (by linarith) (by linarith)]
  rw [h_td_arc, h_pd_arc]
  obtain ⟨h_re_before, h_re_after⟩ :=
    unitArc_log_final s t₀ δ ht₀_Ioo h_s_arc hδ_left hδ_right hδ_pos
  rw [log_div_of_re_pos h_re_before h_re_after]; ring

end
