/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.OnCurvePV.EndpointCorner

/-!
# On-Curve PV: Main Theorem

For any point `s` on `fdBoundaryH H`, the CPV integral of `(z - s)⁻¹` exists.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The curve hits `ρ` at `t = 3`, so if `s ≠ ρ` then `fdBoundaryH H 3 = s` is impossible. -/
private theorem absurd_fdBoundaryH_three_eq {H : ℝ} {s : ℂ} (hs_rho : ¬s = ellipticPointRho)
    (h_eq : fdBoundaryH H 3 = s) : False := by
  rw [fdBoundary_H_at_three] at h_eq
  exact hs_rho h_eq.symm

/-! ### Helper: s = I, H ≤ 1, H < 1 -/

private theorem cpv_exists_at_I_H_lt_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
        (fdBoundaryH H) (3 / 2) (5 / 2) I)
    (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundaryH H t = I ↔ t = 2))
    (h_seg5_ne_I : ∀ {t : ℝ}, 4 < t → t ≤ 5 → fdBoundaryH H t ≠ I)
    (hγ3_ne_I : fdBoundaryH H 3 ≠ I) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundaryH H) 0 5 I := by
  apply cpv_extend_to_full_interval H hH I (3/2) (5/2) (by norm_num) (by norm_num)
    (by norm_num) h_arc_cpv
  · intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1
      rw [h_eq] at this; norm_num [Complex.I_re] at this
    · push Not at ht1
      rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht; linarith [ht.2]
  · intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht; linarith [ht.1]
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · exact hγ3_ne_I h_eq
        · have := fdBoundary_H_seg4_re' H ht3' ht4; rw [h_eq] at this; norm_num at this
      · push Not at ht4
        exact h_seg5_ne_I ht4 ht.2 h_eq

/-! ### Helper: s = I, H = 1 -/

private theorem cpv_exists_at_I_H_eq_one (hH : Real.sqrt 3 / 2 < (1 : ℝ))
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
        (fdBoundaryH 1) (3 / 2) (5 / 2) I)
    (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundaryH 1 t = I ↔ t = 2))
    (hγ3_ne_I : fdBoundaryH 1 3 ≠ I) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundaryH 1) 0 5 I := by
  have hγ92 : fdBoundaryH 1 (9/2) = I := by
    rw [fdBoundary_H_eq_seg5_H (by norm_num : (4 : ℝ) < 9/2)]
    simp [fdBoundarySeg5H]
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundaryH 1) (17/4) (19/4) I := by
    apply cpv_exists_on_smooth_subinterval 1 hH I
      (show (9/2 : ℝ) ∈ Set.Ioo (17/4 : ℝ) (19/4) from ⟨by norm_num, by norm_num⟩) hγ92
    · apply ContDiffAt.congr_of_eventuallyEq _
        (Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 4, Ioi_mem_nhds (by norm_num : (4 : ℝ) < 9/2),
            fun s (hs : 4 < s) => fdBoundary_H_eq_seg5_H hs⟩)
      change ContDiffAt ℝ 2 (fdBoundarySeg5H 1) (9/2 : ℝ)
      unfold fdBoundarySeg5H
      apply ContDiffAt.add
      · exact Complex.ofRealCLM.contDiff.contDiffAt.sub contDiffAt_const
      · exact contDiffAt_const
    · erw [(fdBoundary_H_hasDerivAt_seg5 1 (show (4 : ℝ) < 9/2 from by norm_num)).deriv]
      exact one_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_45 1).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht4 : 4 < t := by linarith [ht.1]
      have ht5 : t ≤ 5 := by linarith [ht.2]
      have h_re_t := fdBoundary_H_seg5_re' 1 ht4 ht5
      have h_re_92 := fdBoundary_H_seg5_re' 1
        (show (4 : ℝ) < 9/2 from by norm_num) (show (9 : ℝ)/2 ≤ 5 from by norm_num)
      have : (fdBoundaryH 1 t).re = (fdBoundaryH 1 (9/2)).re := by rw [hγt]
      linarith
  have h_cpv_0_52 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundaryH 1) 0 (5/2) I := by
    apply cpv_concat _ _ 0 (3/2) (5/2) I
    · apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
      intro t ht h_eq
      by_cases ht1 : t ≤ 1
      · have := fdBoundary_H_seg1_re' 1 ht.1 ht1
        rw [h_eq] at this; norm_num [Complex.I_re] at this
      · push Not at ht1
        rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht; linarith [ht.2]
    · exact h_arc_cpv
    · norm_num
    · norm_num
    · intro ε hε
      exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5/2),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_right (by norm_num))
  have h_cpv_52_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundaryH 1) (5/2) (19/4) I := by
    apply cpv_concat _ _ (5/2) (17/4) (19/4) I
    · apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
      intro t ht h_eq
      by_cases ht3 : t < 3
      · have ht1 : 1 < t := by linarith [ht.1]
        rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht; linarith [ht.1]
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · rcases eq_or_lt_of_le ht3 with rfl | ht3'
          · exact hγ3_ne_I h_eq
          · have := fdBoundary_H_seg4_re' 1 ht3' ht4; rw [h_eq] at this; norm_num at this
        · push Not at ht4
          have := fdBoundary_H_seg5_re' 1 ht4 (by linarith [ht.2])
          rw [h_eq] at this; simp only [Complex.I_re] at this; linarith [ht.2]
    · exact h_seg5_cpv
    · norm_num
    · norm_num
    · intro ε hε
      exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (5/2 : ℝ) ≤ 19/4),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h_cpv_0_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundaryH 1) 0 (19/4) I := by
    apply cpv_concat _ _ 0 (5/2) (19/4) I h_cpv_0_52 h_cpv_52_194
      (by norm_num) (by norm_num)
    intro ε hε
    exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 19/4),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right (by norm_num : (19/4 : ℝ) ≤ 5))
  have h_cpv_194_5 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundaryH 1) (19/4) 5 I := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
    intro t ht h_eq
    have := fdBoundary_H_seg5_re' 1 (lt_of_lt_of_le (by norm_num : (4:ℝ) < 19/4) ht.1) ht.2
    rw [h_eq] at this; simp only [Complex.I_re] at this; linarith [ht.1]
  apply cpv_concat _ _ 0 (19/4) 5 I h_cpv_0_194 h_cpv_194_5
    (by norm_num) (by norm_num)
  intro ε hε; exact fdBoundary_H_cutout_ii 1 hH I ε hε

/-! ### Helper: generic case, t₀ on seg1 (0 < t₀ < 1) -/

private theorem cpv_exists_generic_seg1 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundaryH H t₀ = s)
    (ht₀_ne_0 : t₀ ≠ 0)
    (ht₀_lt_1 : t₀ < 1) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  have ht₀_gt_0 : 0 < t₀ := lt_of_le_of_ne ht₀_mem.1 (Ne.symm ht₀_ne_0)
  apply cpv_extend_to_full_interval H hH s (t₀ / 2) ((t₀ + 1) / 2)
    (by linarith) (by linarith) (by linarith)
  · apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq : fdBoundaryH H =ᶠ[𝓝 t₀]
          (fun t => (1/2 : ℂ) + ↑(H - t * (H - Real.sqrt 3 / 2)) * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht₀_lt_1,
          fun t ht => by
            rw [fdBoundary_H_eq_seg1_H (le_of_lt ht)]
            simp [fdBoundarySeg1H]⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact contDiffAt_const.add ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
          (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const))).mul contDiffAt_const)
    · erw [(fdBoundary_H_hasDerivAt_seg1 H ht₀_lt_1).deriv]
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hH.ne'))
      · exact I_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_01 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht1 : t ≤ 1 := by linarith [ht.2]
      rw [fdBoundary_H_eq_seg1_H ht1,
          fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at hγt
      simp only [fdBoundarySeg1H] at hγt
      have h_im := congr_arg Complex.im hγt
      simp only [one_div, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div, mul_im,
        sub_re, ofReal_re, mul_re, div_ofNat_re, ofReal_im, sub_im, div_ofNat_im, sub_self,
        mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add, sub_right_inj,
        mul_eq_mul_right_iff] at h_im
      rcases h_im with rfl | h_abs
      · rfl
      · linarith
  · intro t ht h_eq
    have ht1 : t ≤ 1 := by linarith [ht.2]
    rw [fdBoundary_H_eq_seg1_H ht1,
        ← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at h_eq
    simp only [fdBoundarySeg1H] at h_eq
    have h_im := congr_arg Complex.im h_eq
    simp only [one_div, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div, mul_im, sub_re,
      ofReal_re, mul_re, div_ofNat_re, ofReal_im, sub_im, div_ofNat_im, sub_self, mul_zero,
      sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add, sub_right_inj,
      mul_eq_mul_right_iff] at h_im
    rcases h_im with rfl | h_abs
    · linarith [ht.2]
    · linarith
  · have h_re_s : s.re = 1/2 := by
      rw [← hγt₀]
      exact fdBoundary_H_seg1_re' H (le_of_lt ht₀_gt_0) (le_of_lt ht₀_lt_1)
    have h_im_s_lt : s.im < H := by
      rw [← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)]
      simp [fdBoundarySeg1H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re]
      nlinarith
    have h_norm_s_gt : 1 < Complex.normSq s := by
      rw [Complex.normSq_apply, h_re_s]
      have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
        rw [← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)]
        simp [fdBoundarySeg1H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re]
        nlinarith
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 from by norm_num),
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
    intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · rw [fdBoundary_H_eq_seg1_H ht1,
          ← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at h_eq
      simp only [fdBoundarySeg1H] at h_eq
      have h_im := congr_arg Complex.im h_eq
      simp only [one_div, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div, mul_im,
        sub_re, ofReal_re, mul_re, div_ofNat_re, ofReal_im, sub_im, div_ofNat_im, sub_self,
        mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add, sub_right_inj,
        mul_eq_mul_right_iff] at h_im
      rcases h_im with rfl | h_abs
      · linarith [ht.1]
      · linarith
    · push Not at ht1
      by_cases ht3 : t < 3
      · have h_norm_arc : Complex.normSq (fdBoundaryH H t) = 1 := by
          rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
        rw [h_eq] at h_norm_arc; linarith
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · rcases eq_or_lt_of_le ht3 with rfl | ht3'
          · rw [fdBoundary_H_at_three] at h_eq; exact hs_rho h_eq.symm
          · have h_re_t := fdBoundary_H_seg4_re' H ht3' ht4
            rw [h_eq] at h_re_t; linarith
        · push Not at ht4
          have h_im_t := fdBoundary_H_seg5_im' H ht4 ht.2
          rw [h_eq] at h_im_t; linarith

/-! ### Helper: generic case, t₀ on arc (1 < t₀ < 3) with seg5 crossing -/

private theorem cpv_exists_generic_arc_seg5_cross (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundaryH H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3)
    (h_re_s_lt : s.re < 1 / 2) (h_re_s_gt : -(1 : ℝ) / 2 < s.re)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundaryH H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s)
    (h_seg5_cross : s.im = H) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  set t₁ := s.re + 9/2 with ht₁_def
  have ht₁_gt4 : 4 < t₁ := by simp [ht₁_def]; linarith [h_re_s_gt]
  have ht₁_lt5 : t₁ < 5 := by simp [ht₁_def]; linarith [h_re_s_lt]
  have hγt₁ : fdBoundaryH H t₁ = s := by
    rw [fdBoundary_H_eq_seg5_H (by linarith : 4 < t₁)]
    apply Complex.ext
    · simp [fdBoundarySeg5H, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, ht₁_def]
    · simp [fdBoundarySeg5H, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        h_seg5_cross]
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₁ + 4) / 2) ((t₁ + 5) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₁
    · have heq_fn : ∀ u ∈ Set.Ioi (4 : ℝ), fdBoundaryH H u =
          (↑(u - 9/2) : ℂ) + ↑H * I := by
        intro u (hu : 4 < u)
        rw [fdBoundary_H_eq_seg5_H hu]
        simp [fdBoundarySeg5H]
      have heq : fdBoundaryH H =ᶠ[𝓝 t₁] (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 4, Ioi_mem_nhds ht₁_gt4, heq_fn⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t₁
        (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const
    · erw [(fdBoundary_H_hasDerivAt_seg5 H ht₁_gt4).deriv]; exact one_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht4 : 4 < t := by linarith [ht.1]
      have ht5 : t ≤ 5 := by linarith [ht.2]
      have h_re_t := fdBoundary_H_seg5_re' H ht4 ht5
      have h_re_t₁ := fdBoundary_H_seg5_re' H ht₁_gt4 (le_of_lt ht₁_lt5)
      have : (fdBoundaryH H t).re = (fdBoundaryH H t₁).re := by rw [hγt]
      linarith
  have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 ((t₀ + 3) / 2) s := by
    apply cpv_concat _ _ 0 ((t₀ + 1) / 2) ((t₀ + 3) / 2) s
    · apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
      intro t ht h_eq
      by_cases ht1 : t ≤ 1
      · have := fdBoundary_H_seg1_re' H ht.1 ht1
        rw [h_eq] at this; linarith
      · push Not at ht1
        have ht3 : t < 3 := by linarith [ht.2]
        have h_ne : t ≠ t₀ := by linarith [ht.2]
        exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
          (by have := h_eq.trans hγt₀.symm
              rwa [fdBoundary_H_eq_arc ht1 ht3,
                fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
    · exact h_arc_cpv
    · linarith
    · linarith
    · intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
        rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ (t₀ + 3) / 2),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_right (by linarith))
  have h_cpv_mid_avoid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₀ + 3) / 2) ((t₁ + 4) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₀ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
        (by have := h_eq.trans hγt₀.symm
            rwa [fdBoundary_H_eq_arc ht1 ht3,
              fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · exact absurd_fdBoundaryH_three_eq hs_rho h_eq
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith
      · push Not at ht4
        have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
        rw [h_eq] at this
        simp [ht₁_def] at *; linarith [ht.2]
  have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₀ + 3) / 2) ((t₁ + 5) / 2) s := by
    apply cpv_concat _ _ ((t₀ + 3) / 2) ((t₁ + 4) / 2) ((t₁ + 5) / 2) s
      h_cpv_mid_avoid h_seg5_cpv (by linarith) (by linarith)
    intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (t₀ + 3) / 2 ≤ (t₁ + 5) / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by linarith) (by linarith))
  have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 ((t₁ + 5) / 2) s := by
    apply cpv_concat _ _ 0 ((t₀ + 3) / 2) ((t₁ + 5) / 2) s
      h_cpv_0_t0h h_cpv_mid (by linarith) (by linarith)
    intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ (t₁ + 5) / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right (by linarith))
  have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₁ + 5) / 2) 5 s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this
    simp [ht₁_def] at *; linarith [ht.1]
  exact cpv_concat _ _ 0 ((t₁ + 5) / 2) 5 s h_cpv_0_t1h h_cpv_end
    (by linarith) (by linarith) (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)

/-! ### Helper: generic case, t₀ on arc (1 < t₀ < 3) without seg5 crossing -/

private theorem cpv_exists_generic_arc_no_cross (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundaryH H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3)
    (h_re_s_lt : s.re < 1 / 2) (h_re_s_gt : -(1 : ℝ) / 2 < s.re)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundaryH H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s)
    (h_seg5_cross : ¬(s.im = H)) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 1) / 2) ((t₀ + 3) / 2)
    (by linarith) (by linarith) (by linarith) h_arc_cpv
  · intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1; rw [h_eq] at this; linarith
    · push Not at ht1
      have ht3 : t < 3 := by linarith [ht.2]
      have h_ne : t ≠ t₀ := by linarith [ht.2]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
        (by have := h_eq.trans hγt₀.symm
            rwa [fdBoundary_H_eq_arc ht1 ht3,
              fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
  · intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₀ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
        (by have := h_eq.trans hγt₀.symm
            rwa [fdBoundary_H_eq_arc ht1 ht3,
              fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · exact absurd_fdBoundaryH_three_eq hs_rho h_eq
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith
      · push Not at ht4
        have := fdBoundary_H_seg5_im' H ht4 ht.2
        rw [h_eq] at this; exact h_seg5_cross this

/-! ### Helper: generic case, t₀ on arc (1 < t₀ < 3), dispatches to cross/no-cross -/

private theorem cpv_exists_generic_arc (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundaryH H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  have h_re_s : s.re = Real.cos (Real.pi * (1 + t₀) / 6) := by
    rw [← hγt₀]; exact fdBoundary_H_arc_re' H ht₀_gt_1 ht₀_lt_3
  have h_im_s_arc : s.im = Real.sin (Real.pi * (1 + t₀) / 6) := by
    rw [← hγt₀]; exact fdBoundary_H_arc_im' H ht₀_gt_1 ht₀_lt_3
  have h_normSq_s : Complex.normSq s = 1 := by
    rw [Complex.normSq_apply, h_re_s, h_im_s_arc]
    linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t₀) / 6)]
  have h_re_s_lt : s.re < 1/2 := by
    rw [h_re_s]
    have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    have := Real.strictAntiOn_cos h2 h1 (by nlinarith [Real.pi_pos])
    linarith [Real.cos_pi_div_three]
  have h_re_s_gt : -(1 : ℝ)/2 < s.re := by
    rw [h_re_s]
    have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h2 : Real.pi * 2 / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩
    have := Real.strictAntiOn_cos h1 h2 (by nlinarith [Real.pi_pos])
    have h_cos23 : Real.cos (Real.pi * 2 / 3) = -(1 : ℝ)/2 := by
      rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]; ring
    linarith
  have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq : fdBoundaryH H =ᶠ[𝓝 t₀]
          (fun u => Complex.exp (↑(Real.pi * (1 + u) / 6) * I)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
          Ioo_mem_nhds ht₀_gt_1 ht₀_lt_3,
          fun u hu => fdBoundary_H_eq_arc hu.1 hu.2⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
        (by fun_prop : ContDiffAt ℝ 2 (fun u : ℝ => Real.pi * (1 + u) / 6) t₀)).mul
          contDiffAt_const).cexp
    · erw [(fdBoundary_H_hasDerivAt_arc H ht₀_gt_1 ht₀_lt_3).deriv]
      apply mul_ne_zero (exp_ne_zero _)
      apply mul_ne_zero
      · exact by norm_num [Complex.ofReal_ne_zero]
      · exact I_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht' : t ∈ Set.Ioo (1 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact arc_angle_injective ht' ⟨ht₀_gt_1, ht₀_lt_3⟩
        (by rw [fdBoundary_H_eq_arc ht'.1 ht'.2,
            fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at hγt; exact hγt)
  by_cases h_seg5_cross : s.im = H
  · exact cpv_exists_generic_arc_seg5_cross H hH s hs_rho t₀ hγt₀
      ht₀_gt_1 ht₀_lt_3 h_re_s_lt h_re_s_gt h_arc_cpv h_seg5_cross
  · exact cpv_exists_generic_arc_no_cross H hH s hs_rho t₀ hγt₀
      ht₀_gt_1 ht₀_lt_3 h_re_s_lt h_re_s_gt h_arc_cpv h_seg5_cross

/-! ### Helper: generic case, t₀ on seg4 (3 < t₀ < 4) -/

private theorem cpv_exists_generic_seg4 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundaryH H t₀ = s)
    (ht₀_gt_3 : 3 < t₀) (ht₀_lt_4 : t₀ < 4) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 3) / 2) ((t₀ + 4) / 2)
    (by linarith) (by linarith) (by linarith)
  · apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq_fn : ∀ u ∈ Set.Ioo (3 : ℝ) 4,
          fdBoundaryH H u = (-(1/2 : ℂ) +
            ↑(Real.sqrt 3 / 2 + (u - 3) * (H - Real.sqrt 3 / 2)) * I) := by
        intro u hu
        rw [fdBoundary_H_eq_seg4_H hu.1 (le_of_lt hu.2)]
        simp [fdBoundarySeg4H]; norm_num
      have heq : fdBoundaryH H =ᶠ[𝓝 t₀] (fun t => -(1/2 : ℂ) +
            ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4,
          Ioo_mem_nhds ht₀_gt_3 ht₀_lt_4, heq_fn⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact contDiffAt_const.add ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
          (contDiffAt_const.add ((contDiffAt_id.sub contDiffAt_const).mul
            contDiffAt_const))).mul contDiffAt_const)
    · erw [(fdBoundary_H_hasDerivAt_seg4 H ht₀_gt_3 ht₀_lt_4).deriv]
      apply mul_ne_zero
      · exact sub_ne_zero.mpr (by exact_mod_cast hH.ne')
      · exact I_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_34 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht3 : 3 < t := by linarith [ht.1]
      have ht4 : t ≤ 4 := by linarith [ht.2]
      have h_im_t : (fdBoundaryH H t).im =
          Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
        rw [fdBoundary_H_eq_seg4_H ht3 ht4]
        simp [fdBoundarySeg4H, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
      have h_im_t₀ : (fdBoundaryH H t₀).im =
          Real.sqrt 3 / 2 + (t₀ - 3) * (H - Real.sqrt 3 / 2) := by
        rw [fdBoundary_H_eq_seg4_H ht₀_gt_3 (le_of_lt ht₀_lt_4)]
        simp [fdBoundarySeg4H, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
      have h_im_eq : (fdBoundaryH H t).im = (fdBoundaryH H t₀).im := by rw [hγt]
      rw [h_im_t, h_im_t₀] at h_im_eq
      have hH_pos : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
      have h_mul_eq : (t - 3) * (H - Real.sqrt 3 / 2) =
          (t₀ - 3) * (H - Real.sqrt 3 / 2) := by linarith
      linarith [mul_right_cancel₀ hH_pos.ne' h_mul_eq]
  · have h_re_s : s.re = -1/2 := by
      rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 (le_of_lt ht₀_lt_4)
    have h_norm_s_gt : 1 < Complex.normSq s := by
      rw [Complex.normSq_apply, h_re_s]
      have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
        rw [← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀)
          (le_of_lt ht₀_lt_4)]
        simp [fdBoundarySeg4H, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
        nlinarith
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 from by norm_num),
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
    intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1; rw [h_eq] at this; linarith
    · push Not at ht1
      by_cases ht3 : t < 3
      · have h_norm_arc : Complex.normSq (fdBoundaryH H t) = 1 := by
          rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
        rw [h_eq] at h_norm_arc; linarith
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · rcases eq_or_lt_of_le ht3 with rfl | ht3'
          · rw [fdBoundary_H_at_three] at h_eq; exact hs_rho h_eq.symm
          · rw [fdBoundary_H_eq_seg4_H (by linarith : 3 < t) ht4,
                ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀)
                (le_of_lt ht₀_lt_4)] at h_eq
            simp only [fdBoundarySeg4H] at h_eq
            have h_im := congr_arg Complex.im h_eq
            simp only [div_ofNat, neg_re, one_re, neg_im, one_im, neg_zero, zero_div, ofReal_re,
              ofReal_im, add_im, mul_im, add_re, mul_re, sub_re, re_ofNat, sub_im, im_ofNat,
              sub_self, mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add,
              add_right_inj, mul_eq_mul_right_iff, sub_left_inj] at h_im
            rcases h_im with rfl | h_abs
            · linarith [ht.2]
            · linarith
        · push Not at ht4; linarith [ht.2]
  · have h_re_s : s.re = -1/2 := by
      rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 (le_of_lt ht₀_lt_4)
    intro t ht h_eq
    by_cases ht4' : 4 < t
    · have := fdBoundary_H_seg5_re' H ht4' ht.2
      rw [h_eq] at this; linarith
    · push Not at ht4'
      have ht3' : 3 < t := by linarith [ht.1]
      by_cases ht4_eq : t = 4
      · subst ht4_eq
        have h_im_eq : s.im = H := by
          rw [← h_eq, fdBoundary_H_at_four]
          simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
                     Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
                     mul_zero, mul_one, neg_zero, zero_add, zero_div, add_zero]
        rw [← hγt₀,
          fdBoundary_H_eq_seg4_H (by linarith) (le_of_lt ht₀_lt_4)] at h_im_eq
        simp [fdBoundarySeg4H] at h_im_eq
        nlinarith
      · rw [fdBoundary_H_eq_seg4_H (by linarith : 3 < t) (by linarith : t ≤ 4),
            ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀)
            (le_of_lt ht₀_lt_4)] at h_eq
        simp only [fdBoundarySeg4H] at h_eq
        have h_im := congr_arg Complex.im h_eq
        simp only [div_ofNat, neg_re, one_re, neg_im, one_im, neg_zero, zero_div, ofReal_re,
          ofReal_im, add_im, mul_im, add_re, mul_re, sub_re, re_ofNat, sub_im, im_ofNat, sub_self,
          mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add, add_right_inj,
          mul_eq_mul_right_iff, sub_left_inj] at h_im
        rcases h_im with rfl | h_abs
        · linarith [ht.1]
        · linarith

/-! ### Helper: generic case, t₀ on seg5 (4 < t₀ < 5) with normSq = 1 -/

private theorem cpv_exists_generic_seg5_normSq_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (t₀ : ℝ)
    (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5)
    (h_im_s : s.im = H) (h_re_s : s.re = t₀ - 9 / 2)
    (h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundaryH H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s)
    (h_normSq : Complex.normSq s = 1) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  have h_re_s_lt : s.re < 1/2 := by linarith [h_re_s]
  have h_re_s_gt : -(1 : ℝ)/2 < s.re := by linarith [h_re_s]
  have h_ivt : s.re ∈ (fun t => Real.cos (Real.pi * (1 + t) / 6)) ''
      Set.Icc (1 : ℝ) 3 := by
    apply intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 3)
    · exact (Real.continuous_cos.comp
        (by fun_prop : Continuous (fun t => Real.pi * (1 + t) / 6))).continuousOn
    · constructor
      · rw [show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 from by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; linarith
      · rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
          Real.cos_pi_div_three]; linarith
  obtain ⟨t₁, ht₁_mem, ht₁_cos⟩ := h_ivt
  simp only [] at ht₁_cos
  have ht₁_gt1 : 1 < t₁ := by
    rcases eq_or_lt_of_le ht₁_mem.1 with rfl | h
    · rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        Real.cos_pi_div_three] at ht₁_cos; linarith
    · exact h
  have ht₁_lt3 : t₁ < 3 := by
    rcases eq_or_lt_of_le ht₁_mem.2 with rfl | h
    · rw [show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at ht₁_cos; linarith
    · exact h
  have hγt₁ : fdBoundaryH H t₁ = s := by
    rw [fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]; exact ht₁_cos
    · rw [Complex.exp_ofReal_mul_I_im]
      have h_sin_pos : 0 < Real.sin (Real.pi * (1 + t₁) / 6) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact (sq_eq_sq₀ (le_of_lt h_sin_pos)
        (by rw [h_im_s]; linarith [hH, Real.sqrt_nonneg 3] : (0 : ℝ) ≤ s.im)).mp (by
        have h1 := Real.sin_sq_add_cos_sq (Real.pi * (1 + t₁) / 6)
        rw [ht₁_cos] at h1
        rw [Complex.normSq_apply] at h_normSq
        nlinarith)
  have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₁ + 1) / 2) ((t₁ + 3) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₁
    · have heq : fdBoundaryH H =ᶠ[𝓝 t₁]
          (fun u => Complex.exp (↑(Real.pi * (1 + u) / 6) * I)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
          Ioo_mem_nhds ht₁_gt1 ht₁_lt3,
          fun u hu => fdBoundary_H_eq_arc hu.1 hu.2⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₁
        (by fun_prop :
          ContDiffAt ℝ 2 (fun u : ℝ =>
            Real.pi * (1 + u) / 6) t₁)).mul
          contDiffAt_const).cexp
    · erw [(fdBoundary_H_hasDerivAt_arc H ht₁_gt1 ht₁_lt3).deriv]
      apply mul_ne_zero (exp_ne_zero _)
      apply mul_ne_zero
      · exact by norm_num [Complex.ofReal_ne_zero]
      · exact I_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht' : t ∈ Set.Ioo (1 : ℝ) 3 :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact arc_angle_injective ht' ⟨ht₁_gt1, ht₁_lt3⟩
        (by rw [fdBoundary_H_eq_arc ht'.1 ht'.2,
            fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at hγt; exact hγt)
  have h_avoid_start : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 ((t₁ + 1) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht0 : t = 0
    · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
    · by_cases ht1 : t ≤ 1
      · have h_im_t : (fdBoundaryH H t).im < H := by
          rw [fdBoundary_H_eq_seg1_H ht1]
          simp [fdBoundarySeg1H, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
          nlinarith [ht.1, lt_of_le_of_ne ht.1 (Ne.symm ht0)]
        rw [h_eq] at h_im_t; linarith [h_im_s]
      · push Not at ht1
        have ht3 : t < 3 := by linarith [ht.2]
        have h_ne : t ≠ t₁ := by linarith [ht.2]
        exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩
          (by have := h_eq.trans hγt₁.symm
              rwa [fdBoundary_H_eq_arc ht1 ht3,
                fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
  have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 ((t₁ + 3) / 2) s := by
    apply cpv_concat _ _ 0 ((t₁ + 1) / 2) ((t₁ + 3) / 2) s
      h_avoid_start h_arc_cpv (by linarith) (by linarith)
    intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ (t₁ + 3) / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right (by linarith))
  have h_avoid_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₁ + 3) / 2) ((t₀ + 4) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₁ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩
        (by have := h_eq.trans hγt₁.symm
            rwa [fdBoundary_H_eq_arc ht1 ht3,
              fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · exact absurd_fdBoundaryH_three_eq hs_rho h_eq
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith [h_re_s]
      · push Not at ht4
        have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
        rw [h_eq] at this; linarith [h_re_s, ht.2]
  have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₁ + 3) / 2) ((t₀ + 5) / 2) s := by
    apply cpv_concat _ _ ((t₁ + 3) / 2) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s
      h_avoid_mid h_seg5_cpv (by linarith) (by linarith)
    intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (t₁ + 3) / 2 ≤ (t₀ + 5) / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by linarith) (by linarith))
  have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 ((t₀ + 5) / 2) s := by
    apply cpv_concat _ _ 0 ((t₁ + 3) / 2) ((t₀ + 5) / 2) s
      h_cpv_0_t1h h_cpv_mid (by linarith) (by linarith)
    intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ (t₀ + 5) / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right (by linarith))
  have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₀ + 5) / 2) 5 s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this; linarith [h_re_s, ht.1]
  exact cpv_concat _ _ 0 ((t₀ + 5) / 2) 5 s h_cpv_0_t0h h_cpv_end
    (by linarith) (by linarith) (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)

/-! ### Helper: generic case, t₀ on seg5 (4 < t₀ < 5) without normSq = 1 -/

private theorem cpv_exists_generic_seg5_normSq_ne_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho)
    (t₀ : ℝ)
    (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5)
    (h_re_s : s.re = t₀ - 9 / 2)
    (h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundaryH H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s)
    (h_normSq : ¬Complex.normSq s = 1)
    (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (h_im_s : s.im = H) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 4) / 2) ((t₀ + 5) / 2)
    (by linarith) (by linarith) (by linarith) h_seg5_cpv
  · intro t ht h_eq
    by_cases ht0 : t = 0
    · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
    · by_cases ht1 : t ≤ 1
      · have h_im_t : (fdBoundaryH H t).im < H := by
          rw [fdBoundary_H_eq_seg1_H ht1]
          simp [fdBoundarySeg1H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re]
          nlinarith [ht.1, lt_of_le_of_ne ht.1 (Ne.symm ht0)]
        rw [h_eq] at h_im_t; linarith [h_im_s]
      · push Not at ht1
        by_cases ht3 : t < 3
        · have h_norm_arc : Complex.normSq (fdBoundaryH H t) = 1 := by
            rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
              Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
            linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
          rw [h_eq] at h_norm_arc; exact h_normSq h_norm_arc
        · push Not at ht3
          by_cases ht4 : t ≤ 4
          · rcases eq_or_lt_of_le ht3 with rfl | ht3'
            · rw [fdBoundary_H_at_three] at h_eq; exact hs_rho h_eq.symm
            · have := fdBoundary_H_seg4_re' H ht3' ht4
              rw [h_eq] at this; linarith [h_re_s]
          · push Not at ht4
            have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
            rw [h_eq] at this; linarith [h_re_s, ht.2]
  · intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this; linarith [h_re_s, ht.1]

/-! ### Helper: generic case, t₀ on seg5 (4 < t₀ < 5), dispatches -/

private theorem cpv_exists_generic_seg5 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundaryH H t₀ = s)
    (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (ht₀_ne_5 : t₀ ≠ 5)
    (ht₀_gt_4 : 4 < t₀) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  have ht₀_lt_5 : t₀ < 5 := lt_of_le_of_ne ht₀_mem.2 ht₀_ne_5
  have h_im_s : s.im = H := by
    rw [← hγt₀]; exact fdBoundary_H_seg5_im' H ht₀_gt_4 (le_of_lt ht₀_lt_5)
  have h_re_s : s.re = t₀ - 9/2 := by
    rw [← hγt₀]; exact fdBoundary_H_seg5_re' H ht₀_gt_4 (le_of_lt ht₀_lt_5)
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq_fn : ∀ u ∈ Set.Ioi (4 : ℝ), fdBoundaryH H u =
          (↑(u - 9/2) : ℂ) + ↑H * I := by
        intro u (hu : 4 < u)
        rw [fdBoundary_H_eq_seg5_H hu]; simp [fdBoundarySeg5H]
      have heq : fdBoundaryH H =ᶠ[𝓝 t₀] (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 4, Ioi_mem_nhds ht₀_gt_4, heq_fn⟩
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
        (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const
    · erw [(fdBoundary_H_hasDerivAt_seg5 H ht₀_gt_4).deriv]; exact one_ne_zero
    · apply (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono
      intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht4 : 4 < t := by linarith [ht.1]
      have ht5 : t ≤ 5 := by linarith [ht.2]
      have h_re_t := fdBoundary_H_seg5_re' H ht4 ht5
      have h_re_t₀ := fdBoundary_H_seg5_re' H ht₀_gt_4 (le_of_lt ht₀_lt_5)
      have : (fdBoundaryH H t).re = (fdBoundaryH H t₀).re := by rw [hγt]
      linarith
  by_cases h_normSq : Complex.normSq s = 1
  · exact cpv_exists_generic_seg5_normSq_one H hH s hs_rho hs_endpoint t₀
      ht₀_gt_4 ht₀_lt_5 h_im_s h_re_s h_seg5_cpv h_normSq
  · exact cpv_exists_generic_seg5_normSq_ne_one H hH s hs_rho t₀
      ht₀_gt_4 ht₀_lt_5 h_re_s h_seg5_cpv h_normSq hs_endpoint h_im_s

/-! ### Main theorem -/

/-- For any point on `fdBoundaryH H`, the CPV integral of `(z - s)⁻¹` exists. -/
theorem fdBoundary_H_cpv_exists_of_onCurve (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (h_on : ∃ t ∈ Set.Icc (0 : ℝ) 5, fdBoundaryH H t = s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  by_cases hs_rho : s = ellipticPointRho
  · subst hs_rho
    obtain ⟨L, hL⟩ := cpv_exists_at_rho H hH
    exact ⟨L, hL.congr (fun ε => rfl)⟩
  by_cases hs_rho' : s = ellipticPointRhoPlusOne
  · subst hs_rho'
    obtain ⟨L, hL⟩ := cpv_exists_at_rho_plus_one H hH
    exact ⟨L, hL.congr (fun ε => rfl)⟩
  by_cases hs_i : s = I
  · subst hs_i
    by_cases hH1 : 1 < H
    · obtain ⟨L, hL⟩ := cpv_exists_at_i H hH1
      exact ⟨L, hL.congr (fun ε => rfl)⟩
    · push Not at hH1
      have hγ2 : fdBoundaryH H 2 = I := by
        rw [fdBoundary_H_eq_arc (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)]
        have : Real.pi * (1 + 2) / 6 = Real.pi / 2 := by ring
        rw [this, show (↑(Real.pi / 2) : ℂ) * I = ↑Real.pi / 2 * I from by push_cast; ring]
        exact Complex.exp_pi_div_two_mul_I
      have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
          (fdBoundaryH H) (3/2) (5/2) I := by
        apply cpv_exists_on_smooth_subinterval H hH I
          (show (2 : ℝ) ∈ Set.Ioo (3/2 : ℝ) (5/2) from ⟨by norm_num, by norm_num⟩) hγ2
        · have heq : fdBoundaryH H =ᶠ[𝓝 2]
              (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
              Ioo_mem_nhds (by norm_num) (by norm_num),
              fun s hs => fdBoundary_H_eq_arc hs.1 hs.2⟩
          apply ContDiffAt.congr_of_eventuallyEq _ heq
          exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp (2 : ℝ)
            (by fun_prop : ContDiffAt ℝ 2 (fun s : ℝ => Real.pi * (1 + s) / 6) (2 : ℝ))).mul
              contDiffAt_const).cexp
        · have hd := fdBoundary_H_hasDerivAt_arc H
            (show (1 : ℝ) < 2 from by norm_num) (show (2 : ℝ) < 3 from by norm_num)
          erw [hd.deriv]
          apply mul_ne_zero (exp_ne_zero _)
          apply mul_ne_zero
          · exact by norm_num [Complex.ofReal_ne_zero]
          · exact I_ne_zero
        · apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
          intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · intro t ht hγt
          have ht' : t ∈ Set.Ioo (1 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
          have h2' : (2 : ℝ) ∈ Set.Ioo (1 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
          rw [fdBoundary_H_eq_arc ht'.1 ht'.2, fdBoundary_H_eq_arc h2'.1 h2'.2] at hγt
          exact arc_angle_injective ht' h2' hγt
      have h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 →
          (fdBoundaryH H t = I ↔ t = 2) := by
        intro t ht1 ht3
        constructor
        · intro h_eq
          have h1 := fdBoundary_H_eq_arc (H := H) ht1 ht3
          have h2 := fdBoundary_H_eq_arc (H := H)
            (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
          exact arc_angle_injective ⟨ht1, ht3⟩ ⟨by norm_num, by norm_num⟩
            ((h1.symm.trans h_eq).trans (h2.symm.trans hγ2).symm)
        · rintro rfl; exact hγ2
      have hγ3_ne_I : fdBoundaryH H 3 ≠ I := by
        rw [fdBoundary_H_at_three H]
        intro h_eq; exact hs_rho h_eq.symm
      have hγ4_ne_I : fdBoundaryH H 4 ≠ I := by
        rw [fdBoundary_H_at_four H]
        intro h_eq; have h_re := congr_arg Complex.re h_eq
        simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
                   Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, sub_zero,
                   Complex.I_im, Complex.ofReal_im, mul_one, Complex.I_re] at h_re
        norm_num at h_re
      rcases lt_or_eq_of_le hH1 with hH_lt | hH_eq
      · exact cpv_exists_at_I_H_lt_one H hH h_arc_cpv
          (fun {t} => h_arc_I_iff)
          (fun {t} ht4 ht5 => by
            intro h_eq
            have := fdBoundary_H_seg5_im' H ht4 ht5
            rw [h_eq] at this; simp only [Complex.I_im] at this; linarith)
          hγ3_ne_I
      · subst hH_eq
        exact cpv_exists_at_I_H_eq_one hH h_arc_cpv
          (fun {t} => h_arc_I_iff) hγ3_ne_I
  · obtain ⟨t₀, ht₀_mem, hγt₀⟩ := h_on
    by_cases hs_endpoint : s = (1/2 : ℂ) + ↑H * I
    · subst hs_endpoint
      exact cpv_at_endpoint H hH
    by_cases hs_corner : s = -(1/2 : ℂ) + ↑H * I
    · subst hs_corner
      exact cpv_at_corner H hH
    · have ht₀_ne_0 : t₀ ≠ 0 := by
        intro h; subst h; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_zero])
      have ht₀_ne_1 : t₀ ≠ 1 := by
        intro h; subst h
        exact hs_rho' (by rw [← hγt₀, fdBoundary_H_at_one])
      have ht₀_ne_3 : t₀ ≠ 3 := by
        intro h; subst h; exact hs_rho (by rw [← hγt₀, fdBoundary_H_at_three])
      have ht₀_ne_4 : t₀ ≠ 4 := by
        intro h; subst h; exact hs_corner (by rw [← hγt₀, fdBoundary_H_at_four]; ring)
      have ht₀_ne_5 : t₀ ≠ 5 := by
        intro h; subst h; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_five])
      rw [Set.mem_Icc] at ht₀_mem
      have hh₀ : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
      by_cases ht₀_lt_1 : t₀ < 1
      · exact cpv_exists_generic_seg1 H hH s hs_rho t₀
          ht₀_mem hγt₀ ht₀_ne_0 ht₀_lt_1
      · push Not at ht₀_lt_1
        have ht₀_gt_1 : 1 < t₀ := lt_of_le_of_ne ht₀_lt_1 (Ne.symm ht₀_ne_1)
        by_cases ht₀_lt_3 : t₀ < 3
        · exact cpv_exists_generic_arc H hH s hs_rho t₀
            hγt₀ ht₀_gt_1 ht₀_lt_3
        · push Not at ht₀_lt_3
          have ht₀_gt_3 : 3 < t₀ := lt_of_le_of_ne ht₀_lt_3 (Ne.symm ht₀_ne_3)
          by_cases ht₀_lt_4 : t₀ < 4
          · exact cpv_exists_generic_seg4 H hH s hs_rho t₀
              hγt₀ ht₀_gt_3 ht₀_lt_4
          · push Not at ht₀_lt_4
            have ht₀_gt_4 : 4 < t₀ := lt_of_le_of_ne ht₀_lt_4 (Ne.symm ht₀_ne_4)
            exact cpv_exists_generic_seg5 H hH s hs_rho t₀
              ht₀_mem hγt₀ hs_endpoint ht₀_ne_5 ht₀_gt_4

end
