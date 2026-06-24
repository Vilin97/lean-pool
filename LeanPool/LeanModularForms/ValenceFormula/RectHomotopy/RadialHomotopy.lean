/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.PolygonSlope
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial homotopy from polygon to unit circle

Constructs the radial homotopy `polygonToCircleRadial` that deforms `fdPolygon`
onto the unit circle around an interior point `p`, and proves all 8 conditions
of `PiecewiseCurvesHomotopicAvoiding`.

* `polygonToCircleRadial` — radial interpolation H(t,s) = p + ((1-s)‖z-p‖+s)(z-p)/‖z-p‖
* `fdPolygonRadialCircle` — the endpoint curve at s=1 (on unit circle around p)
* `fdPolygon_piecewise_homotopic_to_radialCircle` — combined 8-condition proof
* `winding_fdPolygon_eq_radialCircle` — winding numbers are equal
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Radial homotopy from polygon to unit circle around p.
    H(t, s) = p + ((1-s)·‖z-p‖ + s) · (z-p)/‖z-p‖ -/
noncomputable def polygonToCircleRadial (p : ℂ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let z := fdPolygon t
  let dir := z - p
  p + ((1 - s) * ‖dir‖ + s) • (dir / ‖dir‖)

/-- Distance from `fdPolygon t` to an interior point `p` is positive. -/
private lemma fdPolygon_sub_p_norm_pos (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Icc 0 5) : ‖fdPolygon t - p‖ > 0 :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (fdPolygon_avoids_interior p hp_norm hp_re hp_im t ht))

/-- The radial homotopy avoids p when z ≠ p. -/
lemma polygonToCircleRadial_avoids (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Icc 0 5) (s : ℝ) (hs : s ∈ Icc 0 1) :
    polygonToCircleRadial p (t, s) ≠ p := by
  simp only [polygonToCircleRadial]
  have hz_ne : fdPolygon t ≠ p := fdPolygon_avoids_interior p hp_norm hp_re hp_im t ht
  have hdir_ne : fdPolygon t - p ≠ 0 := sub_ne_zero.mpr hz_ne
  have hnorm_pos : ‖fdPolygon t - p‖ > 0 := norm_pos_iff.mpr hdir_ne
  have hcoeff : (1 - s) * ‖fdPolygon t - p‖ + s > 0 := by
    have h1 : (1 - s) * ‖fdPolygon t - p‖ ≥ 0 :=
      mul_nonneg (by linarith [hs.2]) (le_of_lt hnorm_pos)
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · simp only [← hs0, sub_zero, one_mul, add_zero]; exact hnorm_pos
    · linarith
  intro heq
  rw [add_eq_left] at heq
  rw [RCLike.real_smul_eq_coe_mul] at heq
  rcases mul_eq_zero.mp heq with hcoeff_zero | hdir_zero
  · exact ne_of_gt hcoeff (Complex.ofReal_eq_zero.mp hcoeff_zero)
  · rw [div_eq_zero_iff] at hdir_zero
    rcases hdir_zero with h1 | h2
    · exact hdir_ne h1
    · have hnorm_zero : ‖fdPolygon t - p‖ = 0 := Complex.ofReal_eq_zero.mp h2
      exact ne_of_gt hnorm_pos hnorm_zero

/-- The radial circle around p: normalized projection of fdPolygon onto unit circle around p.
    This is polygonToCircleRadial at s=1. -/
noncomputable def fdPolygonRadialCircle (p : ℂ) : ℝ → ℂ := fun t =>
  polygonToCircleRadial p (t, 1)

/-- fdPolygonRadialCircle is on the unit circle around p. -/
lemma fdPolygonRadialCircle_dist (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Icc 0 5) :
    ‖fdPolygonRadialCircle p t - p‖ = 1 := by
  have hnorm_pos : ‖fdPolygon t - p‖ > 0 :=
    fdPolygon_sub_p_norm_pos p hp_norm hp_re hp_im t ht
  simp only [fdPolygonRadialCircle, polygonToCircleRadial, sub_self, zero_mul, zero_add,
    add_sub_cancel_left]
  erw [one_smul]
  rw [norm_div]
  have h_norm_real : ‖(‖fdPolygon t - p‖ : ℂ)‖ = |‖fdPolygon t - p‖| :=
    RCLike.norm_ofReal ‖fdPolygon t - p‖
  rw [h_norm_real, abs_norm, div_self (ne_of_gt hnorm_pos)]

/-- fdPolygonRadialCircle avoids p. -/
lemma fdPolygonRadialCircle_avoids (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Icc 0 5) :
    fdPolygonRadialCircle p t ≠ p := by
  simp only [fdPolygonRadialCircle]
  exact polygonToCircleRadial_avoids p hp_norm hp_re hp_im t ht 1 ⟨by norm_num, le_refl 1⟩

/-- fdPolygon t ≠ p for all t ∈ ℝ under interior hypotheses. -/
lemma fdPolygon_ne_p_everywhere (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) : fdPolygon t ≠ p := by
  intro heq
  by_cases ht1 : t ≤ 1
  · simp only [fdPolygon, ht1, ↓reduceIte] at heq
    have hre : p.re = 1/2 := by rw [← heq]; simp [Complex.add_re, Complex.mul_re]
    linarith [abs_lt.mp hp_re]
  · push Not at ht1
    by_cases ht2 : t ≤ 2
    · simp only [fdPolygon, not_le.mpr ht1, ht2, ↓reduceIte] at heq
      have ht_range : t - 1 ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
      have hin_ball : chordSegment rho' iPoint (t - 1) ∈ closedBall (0 : ℂ) 1 :=
        chord_in_closed_unit_ball rho' iPoint rho'_norm i_point_norm (t - 1) ht_range
      rw [mem_closedBall, dist_zero_right] at hin_ball
      rw [heq] at hin_ball
      linarith
    · push Not at ht2
      by_cases ht3 : t ≤ 3
      · simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, ht3, ↓reduceIte] at heq
        have ht_range : t - 2 ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
        have hin_ball : chordSegment iPoint rho (t - 2) ∈ closedBall (0 : ℂ) 1 :=
          chord_in_closed_unit_ball iPoint rho i_point_norm rho_norm (t - 2) ht_range
        rw [mem_closedBall, dist_zero_right] at hin_ball
        rw [heq] at hin_ball
        linarith
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, not_le.mpr ht3, ht4,
            ↓reduceIte] at heq
          have hre : p.re = -1/2 := by rw [← heq]; simp [Complex.add_re, Complex.mul_re]
          have hp_re' : p.re > -1/2 := by linarith [abs_lt.mp hp_re]
          linarith
        · push Not at ht4
          simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, not_le.mpr ht3,
            not_le.mpr ht4, ↓reduceIte] at heq
          have him : p.im = HHeight := by rw [← heq]; simp [Complex.add_im, Complex.mul_im]
          linarith

/-- Radial homotopy is continuous. -/
lemma polygonToCircleRadial_continuous (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) :
    Continuous (polygonToCircleRadial p) := by
  unfold polygonToCircleRadial
  have hne : ∀ t, fdPolygon t - p ≠ 0 := fun t =>
    sub_ne_zero.mpr (fdPolygon_ne_p_everywhere p hp_norm hp_re hp_im t)
  have hnorm_ne : ∀ t, (‖fdPolygon t - p‖ : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne t))
  have h_dir : Continuous (fun (ts : ℝ × ℝ) => fdPolygon ts.1 - p) :=
    (fdPolygon_continuous.comp continuous_fst).sub continuous_const
  have h_norm_dir : Continuous (fun (ts : ℝ × ℝ) => ‖fdPolygon ts.1 - p‖) :=
    continuous_norm.comp h_dir
  apply Continuous.add continuous_const
  apply Continuous.smul
  · apply Continuous.add
    · exact (continuous_const.sub continuous_snd).mul h_norm_dir
    · exact continuous_snd
  · apply Continuous.div h_dir (continuous_ofReal.comp h_norm_dir)
    intro ⟨t, s⟩; exact hnorm_ne t

/-- At s=0, radial homotopy equals fdPolygon. -/
lemma polygonToCircleRadial_at_s_zero (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Icc 0 5) :
    polygonToCircleRadial p (t, 0) = fdPolygon t := by
  have hnorm_pos : ‖fdPolygon t - p‖ > 0 :=
    fdPolygon_sub_p_norm_pos p hp_norm hp_re hp_im t ht
  have hnorm_ne : (‖fdPolygon t - p‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm_pos)
  simp only [polygonToCircleRadial, sub_zero, one_mul, add_zero]
  calc p + ‖fdPolygon t - p‖ • ((fdPolygon t - p) / ↑‖fdPolygon t - p‖)
      = p + (↑‖fdPolygon t - p‖ : ℂ) * ((fdPolygon t - p) / ↑‖fdPolygon t - p‖) := by
          simp only [Algebra.smul_def]; rfl
    _ = p + (fdPolygon t - p) := by rw [mul_div_cancel₀ _ hnorm_ne]
    _ = fdPolygon t := by ring

/-- At s=1, radial homotopy equals fdPolygonRadialCircle. -/
lemma polygonToCircleRadial_at_s_one (p : ℂ) (t : ℝ) :
    polygonToCircleRadial p (t, 1) = fdPolygonRadialCircle p t := rfl

/-- Radial homotopy is closed at each stage. -/
lemma polygonToCircleRadial_closed (p : ℂ) (_hp_norm : ‖p‖ > 1) (_hp_re : |p.re| < 1 / 2)
    (_hp_im : p.im < HHeight) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    polygonToCircleRadial p (0, s) = polygonToCircleRadial p (5, s) := by
  simp only [polygonToCircleRadial]
  have hclosed : fdPolygon 0 = fdPolygon 5 := fdPolygon_closed
  simp only [hclosed]

/-- Radial homotopy is differentiable in t away from partition points. -/
lemma polygonToCircleRadial_differentiable_off_partition (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Ioo 0 5)
    (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ)) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    DifferentiableAt ℝ (fun t' => polygonToCircleRadial p (t', s)) t := by
  simp only [polygonToCircleRadial]
  have h_diff_fd : DifferentiableAt ℝ fdPolygon t :=
    fdPolygon_differentiableAt_off_partition t ht ht_not_P
  have h_diff_sub : DifferentiableAt ℝ (fun t' => fdPolygon t' - p) t :=
    h_diff_fd.sub (differentiableAt_const p)
  have hz_ne : fdPolygon t ≠ p :=
    fdPolygon_avoids_interior p hp_norm hp_re hp_im t (Ioo_subset_Icc_self ht)
  have hdir_ne : fdPolygon t - p ≠ 0 := sub_ne_zero.mpr hz_ne
  have h_norm_diff : DifferentiableAt ℝ (fun t' => ‖fdPolygon t' - p‖) t :=
    DifferentiableAt.norm ℂ h_diff_sub hdir_ne
  have h_coeff_diff : DifferentiableAt ℝ (fun t' => (1 - s) * ‖fdPolygon t' - p‖ + s) t :=
    ((differentiableAt_const (1 - s)).mul h_norm_diff).add (differentiableAt_const s)
  have h_norm_C_diff : DifferentiableAt ℝ (fun t' => (‖fdPolygon t' - p‖ : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt.comp t h_norm_diff
  have h_norm_C_ne : (‖fdPolygon t - p‖ : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hdir_ne
  have h_unit_diff : DifferentiableAt ℝ
      (fun t' => (fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ)) t :=
    h_diff_sub.div h_norm_C_diff h_norm_C_ne
  exact (differentiableAt_const p).add (h_coeff_diff.smul h_unit_diff)

/-- t-derivative is continuous on each piece. -/
lemma polygonToCircleRadial_deriv_cont_on_piece (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂)
    (hpiece : ∀ t ∈ Ioo p₁ p₂, t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (h_sub : Ioo p₁ p₂ ⊆ Ioo 0 5) :
    ContinuousOn (fun (q : ℝ × ℝ) => deriv (fun t' => polygonToCircleRadial p (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  apply continuousOn_of_forall_continuousAt
  intro ⟨t, s⟩ ⟨ht_mem, hs_mem⟩
  have ht_sub : t ∈ Ioo 0 5 := h_sub ht_mem
  have ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ) := hpiece t ht_mem
  have h_diff : DifferentiableAt ℝ (fun t' => polygonToCircleRadial p (t', s)) t :=
    polygonToCircleRadial_differentiable_off_partition p hp_norm hp_re hp_im t
      ht_sub ht_not_P s hs_mem
  have h_fdPolygon_contDiff : ContDiffAt ℝ 1 fdPolygon t := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht_not_P
    obtain ⟨ht_ne1, ht_ne2, ht_ne3, ht_ne4⟩ := ht_not_P
    by_cases h1 : t < 1
    · have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg1 := by
        filter_upwards [eventually_lt_nhds h1, eventually_gt_nhds ht_sub.1] with u hu1 _
        simp only [fdPolygon, show u ≤ 1 from le_of_lt hu1, if_true, fdPolygonSeg1]
      exact ((contDiff_one_iff_deriv.mpr ⟨fdPolygon_seg1_differentiable,
        by rw [fdPolygon_deriv_seg1]; exact continuous_const⟩).contDiffAt).congr_of_eventuallyEq heq
    · push Not at h1
      by_cases h2 : t < 2
      · have h1' : t > 1 := lt_of_le_of_ne h1 (Ne.symm ht_ne1)
        have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg2 := by
          filter_upwards [eventually_gt_nhds h1', eventually_lt_nhds h2] with u hu1 hu2
          simp only [fdPolygon, not_le.mpr hu1, le_of_lt hu2, if_true, if_false, fdPolygonSeg2]
        exact ((contDiff_one_iff_deriv.mpr ⟨fdPolygon_seg2_differentiable,
          by rw [fdPolygon_deriv_seg2]; exact continuous_const⟩
          ).contDiffAt).congr_of_eventuallyEq heq
      · push Not at h2
        by_cases h3 : t < 3
        · have h2' : t > 2 := lt_of_le_of_ne h2 (Ne.symm ht_ne2)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg3 := by
            filter_upwards [eventually_gt_nhds h2', eventually_lt_nhds h3] with u hu1 hu2
            simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hu1),
              not_le.mpr hu1, le_of_lt hu2, if_true, if_false, fdPolygonSeg3]
          exact ((contDiff_one_iff_deriv.mpr ⟨fdPolygon_seg3_differentiable,
            by rw [fdPolygon_deriv_seg3]; exact continuous_const⟩
            ).contDiffAt).congr_of_eventuallyEq heq
        · push Not at h3
          by_cases h4 : t < 4
          · have h3' : t > 3 := lt_of_le_of_ne h3 (Ne.symm ht_ne3)
            have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg4 := by
              filter_upwards [eventually_gt_nhds h3', eventually_lt_nhds h4] with u hu1 hu2
              simp only [fdPolygon,
                not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hu1),
                not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hu1),
                not_le.mpr hu1, le_of_lt hu2, if_true, if_false, fdPolygonSeg4]
            exact ((contDiff_one_iff_deriv.mpr ⟨fdPolygon_seg4_differentiable,
              by rw [fdPolygon_deriv_seg4]; exact continuous_const⟩
              ).contDiffAt).congr_of_eventuallyEq heq
          · push Not at h4
            have h4' : t > 4 := lt_of_le_of_ne h4 (Ne.symm ht_ne4)
            have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg5 := by
              filter_upwards [eventually_gt_nhds h4', eventually_lt_nhds ht_sub.2] with u hu1 _
              simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hu1),
                not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hu1),
                not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hu1),
                not_le.mpr hu1, if_false, fdPolygonSeg5]
            exact ((contDiff_one_iff_deriv.mpr ⟨fdPolygon_seg5_differentiable,
              by rw [fdPolygon_deriv_seg5]; exact continuous_const⟩
              ).contDiffAt).congr_of_eventuallyEq heq
  have hz_ne : fdPolygon t ≠ p :=
    fdPolygon_avoids_interior p hp_norm hp_re hp_im t (Ioo_subset_Icc_self ht_sub)
  have hdir_ne : fdPolygon t - p ≠ 0 := sub_ne_zero.mpr hz_ne
  have h_fd_joint : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => fdPolygon q.1) (t, s) :=
    h_fdPolygon_contDiff.comp (t, s) contDiffAt_fst
  have h_dir_joint : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => fdPolygon q.1 - p) (t, s) :=
    h_fd_joint.sub contDiffAt_const
  have h_norm_joint : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => ‖fdPolygon q.1 - p‖) (t, s) :=
    h_dir_joint.norm ℝ hdir_ne
  have h_norm_C_joint : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (‖fdPolygon q.1 - p‖ : ℂ)) (t, s) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (t, s) h_norm_joint
  have h_coeff_joint : ContDiffAt ℝ 1
      (fun q : ℝ × ℝ => (1 - q.2) * ‖fdPolygon q.1 - p‖ + q.2) (t, s) :=
    ((contDiffAt_const.sub contDiffAt_snd).mul h_norm_joint).add contDiffAt_snd
  have h_norm_C_ne : (‖fdPolygon t - p‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hdir_ne)
  have h_inv_norm_C : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => ((‖fdPolygon q.1 - p‖ : ℂ))⁻¹) (t, s) :=
    h_norm_C_joint.inv h_norm_C_ne
  have h_unit_joint : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (fdPolygon q.1 - p) *
        ((‖fdPolygon q.1 - p‖ : ℂ))⁻¹) (t, s) :=
    h_dir_joint.mul h_inv_norm_C
  have h_explicit_c1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
      p + ((1 - q.2) * ‖fdPolygon q.1 - p‖ + q.2) • ((fdPolygon q.1 - p) *
          ((‖fdPolygon q.1 - p‖ : ℂ))⁻¹)) (t, s) :=
    contDiffAt_const.add (h_coeff_joint.smul h_unit_joint)
  have h_joint_c1 : ContDiffAt ℝ 1 (polygonToCircleRadial p) (t, s) := by
    apply h_explicit_c1.congr_of_eventuallyEq
    filter_upwards with q
    simp only [polygonToCircleRadial, div_eq_mul_inv]
  have h_fderiv_cont : ContinuousAt (fderiv ℝ (polygonToCircleRadial p)) (t, s) :=
    (h_joint_c1.of_le (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).fderiv_right_succ.continuousAt
  have h_eventually_diff : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, s),
      DifferentiableAt ℝ (polygonToCircleRadial p) q := by
    have h_ev_c1 :=
      h_joint_c1.eventually (WithTop.coe_injective.ne WithTop.coe_ne_top)
    exact h_ev_c1.mono (fun q hq => hq.differentiableAt one_ne_zero)
  have h_deriv_eq_fderiv : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, s),
      deriv (fun t' => polygonToCircleRadial p (t', q.2)) q.1 =
        fderiv ℝ (polygonToCircleRadial p) q ((1 : ℝ), (0 : ℝ)) := by
    filter_upwards [h_eventually_diff] with q hq
    have h_mk : HasDerivAt (fun t' => (t', q.2)) ((1 : ℝ), (0 : ℝ)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    have h_fderiv_at : HasFDerivAt (polygonToCircleRadial p)
        (fderiv ℝ (polygonToCircleRadial p) q) q :=
      hq.hasFDerivAt
    exact (h_fderiv_at.comp_hasDerivAt q.1 h_mk).deriv
  have h_eval_cont : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (polygonToCircleRadial p) q ((1 : ℝ), (0 : ℝ))) (t, s) :=
    (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ))).continuous.continuousAt.comp
      h_fderiv_cont
  exact h_eval_cont.congr (h_deriv_eq_fderiv.mono fun q hq => hq.symm)

/-- Normalization is Lipschitz: ‖w₁/‖w₁‖ - w₂/‖w₂‖‖ ≤ 2·‖w₁ - w₂‖/δ
    when ‖w₁‖ ≥ δ and ‖w₂‖ ≥ δ. -/
lemma norm_normalize_sub_le {w₁ w₂ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hw₁ : δ ≤ ‖w₁‖) (hw₂ : δ ≤ ‖w₂‖) :
    ‖w₁ / (‖w₁‖ : ℂ) - w₂ / (‖w₂‖ : ℂ)‖ ≤ 2 * ‖w₁ - w₂‖ / δ := by
  have h1_pos : (0 : ℝ) < ‖w₁‖ := lt_of_lt_of_le hδ hw₁
  have h2_pos : (0 : ℝ) < ‖w₂‖ := lt_of_lt_of_le hδ hw₂
  have hdecomp : w₁ / (‖w₁‖ : ℂ) - w₂ / (‖w₂‖ : ℂ) = (w₁ - w₂) / (‖w₁‖ : ℂ) +
        w₂ * ((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ)) / ((‖w₁‖ : ℂ) * (‖w₂‖ : ℂ)) := by
    have h1c : (‖w₁‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1_pos)
    have h2c : (‖w₂‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h2_pos)
    field_simp
    ring
  have hterm1 : ‖(w₁ - w₂) / (‖w₁‖ : ℂ)‖ ≤ ‖w₁ - w₂‖ / δ := by
    have h_eq : ‖(w₁ - w₂) / (‖w₁‖ : ℂ)‖ = ‖w₁ - w₂‖ / ‖w₁‖ := by
      rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt h1_pos)]
    rw [h_eq]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hw₁
  have hterm2 : ‖w₂ * ((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ)) / ((‖w₁‖ : ℂ) * (‖w₂‖ : ℂ))‖ ≤ ‖w₁ - w₂‖ / δ := by
    have h_eq : ‖w₂ * ((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ)) / ((‖w₁‖ : ℂ) * (‖w₂‖ : ℂ))‖ =
        ‖w₂‖ * ‖((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ))‖ / (‖w₁‖ * ‖w₂‖) := by
      rw [norm_div, norm_mul, norm_mul, norm_real, norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (le_of_lt h1_pos), abs_of_nonneg (le_of_lt h2_pos)]
    rw [h_eq,
      show ‖w₂‖ * ‖((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ))‖ =
        ‖((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ))‖ * ‖w₂‖ from mul_comm _ _,
      mul_div_mul_right _ _ (ne_of_gt h2_pos)]
    have h_norm_sub_bound :
        ‖((‖w₂‖ : ℂ) - (‖w₁‖ : ℂ))‖ ≤ ‖w₁ - w₂‖ := by
      rw [← Complex.ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact abs_norm_sub_norm_le w₁ w₂
    exact le_trans (div_le_div_of_nonneg_right h_norm_sub_bound (le_of_lt h1_pos))
      (div_le_div_of_nonneg_left (norm_nonneg _) hδ hw₁)
  rw [hdecomp]
  calc ‖(w₁ - w₂) / ↑‖w₁‖ +
        w₂ * (↑‖w₂‖ - ↑‖w₁‖) / (↑‖w₁‖ * ↑‖w₂‖)‖
      ≤ ‖(w₁ - w₂) / ↑‖w₁‖‖ +
        ‖w₂ * (↑‖w₂‖ - ↑‖w₁‖) / (↑‖w₁‖ * ↑‖w₂‖)‖ := norm_add_le _ _
    _ ≤ ‖w₁ - w₂‖ / δ + ‖w₁ - w₂‖ / δ := add_le_add hterm1 hterm2
    _ = 2 * ‖w₁ - w₂‖ / δ := by ring

/-- Right derivative of fdPolygon at each point.
    At partition points {1,2,3,4}, uses the NEXT segment's derivative. -/
noncomputable def fdPolygonRightDeriv (x : ℝ) : ℂ :=
  if x < 1 then deriv fdPolygonSeg1 x
  else if x < 2 then deriv fdPolygonSeg2 x
  else if x < 3 then deriv fdPolygonSeg3 x
  else if x < 4 then deriv fdPolygonSeg4 x
  else deriv fdPolygonSeg5 x

/-- The right derivative of fdPolygon has norm ≤ 3 everywhere. -/
lemma fdPolygon_right_deriv_norm_le (x : ℝ) :
    ‖fdPolygonRightDeriv x‖ ≤ 3 := by
  simp only [fdPolygonRightDeriv]
  split_ifs with h1 h2 h3 h4
  · simp only [fdPolygon_deriv_seg1]
    have h1 : (↑HHeight : ℂ) - ↑(Real.sqrt 3) / 2 = 1 := by simp only [HHeight]; push_cast; ring
    rw [h1]; simp [Complex.norm_I]
  · rw [fdPolygon_deriv_seg2]
    calc ‖iPoint - rho'‖ ≤ ‖iPoint‖ + ‖rho'‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [i_point_norm, rho'_norm]
      _ ≤ 3 := by norm_num
  · rw [fdPolygon_deriv_seg3]
    calc ‖rho - iPoint‖ ≤ ‖(rho : ℂ)‖ + ‖iPoint‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [rho_norm, i_point_norm]
      _ ≤ 3 := by norm_num
  · simp only [fdPolygon_deriv_seg4]
    have h1 : (↑HHeight : ℂ) - ↑(Real.sqrt 3) / 2 = 1 := by simp only [HHeight]; push_cast; ring
    rw [h1]; simp [Complex.norm_I]
  · rw [fdPolygon_deriv_seg5]; simp only [norm_one]; norm_num

/-- fdPolygon has a right derivative at every point. -/
lemma fdPolygon_hasDerivWithinAt_Ici (x : ℝ) :
    HasDerivWithinAt fdPolygon (fdPolygonRightDeriv x) (Ici x) x := by
  simp only [fdPolygonRightDeriv]
  split_ifs with h1 h2 h3 h4
  · have heq : fdPolygon =ᶠ[𝓝[Ici x] x] fdPolygonSeg1 := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h1)] with t ht
      simp only [fdPolygon, fdPolygonSeg1, show t ≤ 1 from le_of_lt ht, ite_true]
    exact (fdPolygon_seg1_differentiable.differentiableAt.hasDerivAt.hasDerivWithinAt
      ).congr_of_eventuallyEq heq
      (by simp only [fdPolygon, fdPolygonSeg1, show x ≤ 1 from le_of_lt h1, ite_true])
  · push Not at h1
    have heq : fdPolygon =ᶠ[𝓝[Ici x] x] fdPolygonSeg2 := by
      filter_upwards [Ico_mem_nhdsGE h2] with t ht
      obtain ⟨ht_ge, ht_lt⟩ := ht
      simp only [fdPolygon, fdPolygonSeg2]
      split_ifs with h'₁ h'₂ h'₃ h'₄
      · have : t = 1 := le_antisymm h'₁ (h1.trans ht_ge)
        subst this; simp [chordSegment, rho', HHeight, iPoint]
      · rfl
      all_goals linarith
    exact (fdPolygon_seg2_differentiable.differentiableAt.hasDerivAt.hasDerivWithinAt
      ).congr_of_eventuallyEq heq
      (by simp only [fdPolygon, fdPolygonSeg2]
          split_ifs with h'₁ h'₂ h'₃ h'₄
          · have : x = 1 := le_antisymm h'₁ h1; subst this
            simp [chordSegment, rho', HHeight, iPoint]
          · rfl
          all_goals linarith)
  · push Not at h1 h2
    have heq : fdPolygon =ᶠ[𝓝[Ici x] x] fdPolygonSeg3 := by
      filter_upwards [Ico_mem_nhdsGE h3] with t ht
      obtain ⟨ht_ge, ht_lt⟩ := ht
      simp only [fdPolygon, fdPolygonSeg3]
      split_ifs with h'₁ h'₂ h'₃ h'₄
      · linarith [h2.trans ht_ge]
      · have : t = 2 := le_antisymm h'₂ (h2.trans ht_ge)
        subst this; simp [chordSegment, rho, iPoint]; ring
      · rfl
      all_goals linarith
    exact (fdPolygon_seg3_differentiable.differentiableAt.hasDerivAt.hasDerivWithinAt
      ).congr_of_eventuallyEq heq
      (by simp only [fdPolygon, fdPolygonSeg3]
          split_ifs with h'₁ h'₂ h'₃ h'₄
          · linarith
          · have : x = 2 := le_antisymm h'₂ h2; subst this
            simp [chordSegment, rho, iPoint]; ring
          · rfl
          all_goals linarith)
  · push Not at h1 h2 h3
    have heq : fdPolygon =ᶠ[𝓝[Ici x] x] fdPolygonSeg4 := by
      filter_upwards [Ico_mem_nhdsGE h4] with t ht
      obtain ⟨ht_ge, ht_lt⟩ := ht
      simp only [fdPolygon, fdPolygonSeg4]
      split_ifs with h'₁ h'₂ h'₃ h'₄
      · linarith [h3.trans ht_ge]
      · linarith [h3.trans ht_ge]
      · have : t = 3 := le_antisymm h'₃ (h3.trans ht_ge)
        subst this
        simp [chordSegment, rho, iPoint, HHeight]; ring
      · rfl
      all_goals linarith
    exact (fdPolygon_seg4_differentiable.differentiableAt.hasDerivAt.hasDerivWithinAt
      ).congr_of_eventuallyEq heq
      (by simp only [fdPolygon, fdPolygonSeg4]
          split_ifs with h'₁ h'₂ h'₃ h'₄
          · linarith
          · linarith
          · have : x = 3 := le_antisymm h'₃ h3; subst this
            simp [chordSegment, rho, iPoint, HHeight]; ring
          · rfl
          all_goals linarith)
  · push Not at h1 h2 h3 h4
    have heq : fdPolygon =ᶠ[𝓝[Ici x] x] fdPolygonSeg5 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hxt : x ≤ t := ht
      simp only [fdPolygon, fdPolygonSeg5]
      split_ifs with h'₁ h'₂ h'₃ h'₄
      · linarith
      · linarith
      · linarith
      · have : t = 4 := le_antisymm h'₄ (h4.trans hxt)
        subst this; simp [HHeight]; ring
      · rfl
    exact (fdPolygon_seg5_differentiable.differentiableAt.hasDerivAt.hasDerivWithinAt
      ).congr_of_eventuallyEq heq
      (by simp only [fdPolygon, fdPolygonSeg5]
          split_ifs with h'₁ h'₂ h'₃ h'₄
          · linarith
          · linarith
          · linarith
          · have : x = 4 := le_antisymm h'₄ h4; subst this
            simp [HHeight]; ring
          · rfl)

/-- fdPolygon is Lipschitz with constant 3. -/
lemma fdPolygon_norm_sub_le (a b : ℝ) :
    ‖fdPolygon b - fdPolygon a‖ ≤ 3 * |b - a| := by
  wlog h : a ≤ b with H
  · rw [norm_sub_rev, abs_sub_comm]; exact H b a (le_of_not_ge h)
  rw [abs_of_nonneg (sub_nonneg.mpr h)]
  have := norm_image_sub_le_of_norm_deriv_right_le_segment
    fdPolygon_continuous.continuousOn (fun x _ => fdPolygon_hasDerivWithinAt_Ici x)
    (fun x _ => fdPolygon_right_deriv_norm_le x) b (right_mem_Icc.mpr h)
  linarith

/-- t-derivative is bounded. -/
lemma polygonToCircleRadial_deriv_bounded (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    ∃ M : ℝ, ∀ t ∈ Icc 0 5, ∀ s ∈ Icc 0 1,
      ‖deriv (fun t' => polygonToCircleRadial p (t', s)) t‖ ≤ M := by
  have h_dist_cont : Continuous (fun t => ‖fdPolygon t - p‖) :=
    continuous_norm.comp (fdPolygon_continuous.sub continuous_const)
  have h_dist_pos : ∀ t ∈ Icc (0 : ℝ) 5, 0 < ‖fdPolygon t - p‖ :=
    fun t ht => fdPolygon_sub_p_norm_pos p hp_norm hp_re hp_im t ht
  obtain ⟨t_min, ht_min_mem, ht_min_le⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 5))
      h_dist_cont.continuousOn
  set δ := ‖fdPolygon t_min - p‖ with hδ_def
  have hδ_pos : 0 < δ := h_dist_pos t_min ht_min_mem
  have hδ_le : ∀ t ∈ Icc (0 : ℝ) 5, δ ≤ ‖fdPolygon t - p‖ :=
    fun t ht => ht_min_le ht
  use (3 + 4 / δ) * 3
  intro t ht s hs
  by_cases hd : DifferentiableAt ℝ (fun t' => polygonToCircleRadial p (t', s)) t
  · apply norm_deriv_le_of_lip' (by positivity : 0 ≤ (3 + 4 / δ) * 3)
    have hg_eq : ∀ t', polygonToCircleRadial p (t', s) =
        p + (1 - s) • (fdPolygon t' - p) +
          s • ((fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ)) := by
      intro t'
      simp only [polygonToCircleRadial]
      set dir := fdPolygon t' - p with hdir
      by_cases hdir_ne : dir = 0
      · simp [hdir_ne]
      · have hnorm_ne : (‖dir‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hdir_ne)
        erw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul,
          RCLike.real_smul_eq_coe_mul]
        push_cast
        have hmdc : ↑‖dir‖ * (dir / ↑‖dir‖) = dir := mul_div_cancel₀ _ hnorm_ne
        rw [add_mul, mul_assoc]; erw [hmdc]; rw [add_assoc]
    have hg_diff : ∀ t',
        polygonToCircleRadial p (t', s) - polygonToCircleRadial p (t, s) =
        (1 - s) • (fdPolygon t' - fdPolygon t) +
        s • ((fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ) -
             (fdPolygon t - p) / (‖fdPolygon t - p‖ : ℂ)) := by
      intro t'
      rw [hg_eq t', hg_eq t]
      have h_cancel : ∀ (a b c d e : ℂ),
          a + b + c - (a + d + e) = (b - d) + (c - e) := by intros; ring
      rw [h_cancel]
      simp only [RCLike.real_smul_eq_coe_mul]
      push_cast
      ring
    have h_norm_ge : ∀ᶠ t' in 𝓝 t, δ / 2 ≤ ‖fdPolygon t' - p‖ :=
      (fdPolygon_continuous.sub continuous_const).norm.continuousAt.preimage_mem_nhds
        (Ici_mem_nhds (by linarith [hδ_le t ht] : δ / 2 < ‖fdPolygon t - p‖))
    filter_upwards [h_norm_ge] with t' ht'_delta
    rw [Real.norm_eq_abs]
    calc ‖(fun t' => polygonToCircleRadial p (t', s)) t' -
          (fun t' => polygonToCircleRadial p (t', s)) t‖
        = ‖polygonToCircleRadial p (t', s) -
            polygonToCircleRadial p (t, s)‖ := rfl
      _ = ‖(1 - s) • (fdPolygon t' - fdPolygon t) +
          s • ((fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ) -
               (fdPolygon t - p) / (‖fdPolygon t - p‖ : ℂ))‖ := by rw [hg_diff t']
      _ ≤ ‖(1 - s) • (fdPolygon t' - fdPolygon t)‖ +
          ‖s • ((fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ) -
               (fdPolygon t - p) / (‖fdPolygon t - p‖ : ℂ))‖ := norm_add_le _ _
      _ = |1 - s| * ‖fdPolygon t' - fdPolygon t‖ +
          |s| * ‖(fdPolygon t' - p) / (‖fdPolygon t' - p‖ : ℂ) -
               (fdPolygon t - p) / (‖fdPolygon t - p‖ : ℂ)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ |1 - s| * ‖fdPolygon t' - fdPolygon t‖ +
          |s| * (4 * ‖fdPolygon t' - fdPolygon t‖ / δ) := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left
          · have h_nsub := norm_normalize_sub_le (half_pos hδ_pos)
              ht'_delta (le_trans (by linarith : δ / 2 ≤ δ) (hδ_le t ht))
            rw [show fdPolygon t' - p - (fdPolygon t - p) =
              fdPolygon t' - fdPolygon t from by ring] at h_nsub
            calc ‖(fdPolygon t' - p) / ↑‖fdPolygon t' - p‖ -
                  (fdPolygon t - p) / ↑‖fdPolygon t - p‖‖
                ≤ 2 * ‖fdPolygon t' - fdPolygon t‖ / (δ / 2) :=
                  h_nsub
              _ = 4 * ‖fdPolygon t' - fdPolygon t‖ / δ := by
                  have hd : δ ≠ 0 := ne_of_gt hδ_pos
                  field_simp; ring
          · exact abs_nonneg _
      _ ≤ 1 * ‖fdPolygon t' - fdPolygon t‖ +
          1 * (4 * ‖fdPolygon t' - fdPolygon t‖ / δ) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right
            · rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
            · exact norm_nonneg _
          · apply mul_le_mul_of_nonneg_right
            · rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
            · positivity
      _ = (1 + 4 / δ) * ‖fdPolygon t' - fdPolygon t‖ := by ring
      _ ≤ (3 + 4 / δ) * ‖fdPolygon t' - fdPolygon t‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          linarith
      _ ≤ (3 + 4 / δ) * (3 * |t' - t|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_lip := fdPolygon_norm_sub_le t' t
          rwa [norm_sub_rev, abs_sub_comm] at h_lip
      _ = (3 + 4 / δ) * 3 * |t' - t| := by ring
  · simp only [deriv_zero_of_not_differentiableAt hd, norm_zero]
    positivity

/-- Radial homotopy satisfies PiecewiseCurvesHomotopicAvoiding. -/
lemma fdPolygon_piecewise_homotopic_to_radialCircle (p : ℂ)
    (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    PiecewiseCurvesHomotopicAvoiding fdPolygon (fdPolygonRadialCircle p) 0 5 p
      ({1, 2, 3, 4} : Finset ℝ) := by
  exact ⟨polygonToCircleRadial p, polygonToCircleRadial_continuous p hp_norm hp_re hp_im,
    fun t ht => polygonToCircleRadial_at_s_zero p hp_norm hp_re hp_im t ht,
    fun t _ht => rfl,
    fun s hs => polygonToCircleRadial_closed p hp_norm hp_re hp_im s hs,
    fun t ht s hs => polygonToCircleRadial_avoids p hp_norm hp_re hp_im t ht s hs,
    fun t ht ht_not_P s hs =>
      polygonToCircleRadial_differentiable_off_partition p hp_norm hp_re hp_im t ht ht_not_P s hs,
    fun p₁ p₂ hp₁p₂ hpiece h_sub =>
      polygonToCircleRadial_deriv_cont_on_piece p hp_norm hp_re hp_im p₁ p₂ hp₁p₂ hpiece h_sub,
    polygonToCircleRadial_deriv_bounded p hp_norm hp_re hp_im⟩

/-- winding(fdPolygon) = winding(fdPolygonRadialCircle). -/
lemma winding_fdPolygon_eq_radialCircle (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' fdPolygon 0 5 p =
    generalizedWindingNumber' (fdPolygonRadialCircle p) 0 5 p := by
  have hab : (0 : ℝ) < 5 := by norm_num
  exact windingNumber_eq_of_piecewise_homotopic fdPolygon (fdPolygonRadialCircle p) 0 5 p
    ({1, 2, 3, 4} : Finset ℝ) hab (fdPolygon_piecewise_homotopic_to_radialCircle p hp_norm hp_re
      hp_im)

end RectHomotopyProof
